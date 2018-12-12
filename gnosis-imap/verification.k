requires "evm-symbolic.k"
requires "../lemmas.k"

module VERIFICATION
    imports EVM-SYMBOLIC
    imports EDSL
    imports LEMMAS

  // ########################
  // Memory Usage
  // ########################

    rule #memoryUsageUpdate(#memoryUsageUpdate(MU, START0, WIDTH0), START1, WIDTH1) => #memoryUsageUpdate(MU, START0, WIDTH0)
      requires START1 +Int WIDTH1 <Int START0 +Int WIDTH0

    rule #memoryUsageUpdate(#memoryUsageUpdate(MU, START0, WIDTH0), START1, WIDTH1) => #memoryUsageUpdate(MU, START1, WIDTH1)
      requires START0 +Int WIDTH0 <=Int START1 +Int WIDTH1

    rule 0 <=Int #memoryUsageUpdate(MU, START, WIDTH) => true

    rule pow256 <=Int #memoryUsageUpdate(MU, START, WIDTH) => false  requires START +Int WIDTH <Int 3705346855594118253554271520278013051304639509300498049262642688253220148477921
    rule #memoryUsageUpdate(MU, START, WIDTH) <Int  pow256 => true   requires START +Int WIDTH <Int 3705346855594118253554271520278013051304639509300498049262642688253220148477921


  // ########################
  // Gas
  // ########################

    syntax Int ::= #gas ( Int , Int ) [function]
 // --------------------------------------------
    rule #gas(NONMEM, MEM) -Int #symCmem(MEM') => #gas(NONMEM, MEM +Int MEM')
    rule #gas(NONMEM, MEM) -Int NONMEM' => #gas(NONMEM +Int NONMEM', MEM)  requires #getKLabelString(NONMEM') =/=String "#symCmem"

    rule G <=Int #gas(_,_)  => true  requires #getKLabelString(G) =/=String "#gas"
    rule #gas(_, _) <Int G  => false requires #getKLabelString(G) =/=String "#gas"

    rule 3000 <=Int #symCcallgas(_, _, _, _, _) => true
    rule #symCcallgas(_, _, _, _, _) <Int 3000 => false

  // ########################
  // Account Map
  // ########################

    syntax Int ::= "#MASTER_COPY_ID" [function]
    syntax Int ::= "#PROXY_ID" [function]
    syntax Int ::= "#ORIGIN_ID" [function]


  // ########################
  // Memory Reasoning
  // ########################

    // Merge
    rule storeRange(storeRange(M, MS0, MW0, #bufSeg(BUF, BS0, BW0)), MS1, MW1, #bufSeg(BUF, BS1, BW1))
        => storeRange(M, MS0, MW0 +Int MW1, #bufSeg(BUF, BS0, MW0 +Int MW1))
      requires #isBuf(BUF) andBool MW0 ==Int BW0 andBool MW1 ==Int BW1
       andBool MS1 ==Int MS0 +Int MW0 andBool BS1 ==Int BS0 +Int BW0

    // select/store key equality

    rule hash2(A,B) ==K I => false
      requires #isConcrete(I)
       andBool I <Int 20 //random small-ish number bigger than any fixed storage location

    rule I ==K hash2(A,B) => hash2(A,B) ==K I
      requires #isConcrete(I)

    rule hash2(A1,B1) ==K hash2(A2,B2) => A1 ==Int A2 andBool B1 ==Int B2

  // ########################
  // Buffer Reasoning
  // ########################

    rule #noOverflowAux(BUF) => true requires #isBuf(BUF)
    rule #noOverflowAux(WS1 ++ WS2) => #noOverflowAux(WS1) andBool #noOverflowAux(WS2)

    rule #bufSeg(BUF, S0, W0) ++ #bufSeg(BUF, S1, W1) => #bufSeg(BUF, S0, W0 +Int W1)
      requires S1 ==Int S0 +Int W0

    rule #bufSeg(BUF, S0, W0) ++ (#bufSeg(BUF, S1, W1) ++ WS) => #bufSeg(BUF, S0, W0 +Int W1) ++ WS
      requires S1 ==Int S0 +Int W0

    rule WS ++ .WordStack => WS

    rule sizeWordStackAux(WS, N) <Int SIZE => sizeWordStackAux(WS, 0) +Int N <Int SIZE  requires N =/=Int 0
    rule SIZELIMIT <Int sizeWordStackAux(WS, N) +Int DELTA  => SIZELIMIT <Int (sizeWordStackAux(WS, 0) +Int N) +Int DELTA  requires N =/=Int 0
    rule SIZELIMIT <Int sizeWordStackAux(WS, N) => SIZELIMIT <Int sizeWordStackAux(WS, 0) +Int N  requires N =/=Int 0


  // ########################
  // Range
  // ########################

    rule 0 <=Int (X modInt Y)         => true
    rule         (X modInt Y) <Int Y  => true  requires Y >Int 0

    rule 0 <=Int 2 ^Int X             => true
    rule         2 ^Int X <Int pow256 => true  requires X <Int 256

    rule 0 <=Int X &Int Y             => true  requires #rangeUInt(256, X) andBool #rangeUInt(256, Y)
    rule         X &Int Y <Int pow256 => true  requires #rangeUInt(256, X) andBool #rangeUInt(256, Y)

    rule 0 <=Int X |Int Y             => true  requires #rangeUInt(256, X) andBool #rangeUInt(256, Y)
    rule         X |Int Y <Int pow256 => true  requires #rangeUInt(256, X) andBool #rangeUInt(256, Y)

    rule 0 <=Int #blockhash(_, _, _, _)             => true
    rule         #blockhash(_, _, _, _) <Int pow256 => true

    //case 0 is never wrapped into #symEcrec(), corresponds to #ecrecEmpty(DATA) == true
    rule 0 <Int   #symEcrec(DATA)             => true

    //that's because the result in concrete semantics is trimmed to Address range.
    rule          #symEcrec(DATA) <Int pow160 => true

    rule 0 <=Int #bufElm(_, _)  => true
    rule #bufElm(_, _) <Int 256 => true

  // ########################
  // Simplification
  // ########################

    rule (X +Int 31) /Int 32 *Int 32 => #ceil32(X)
    rule (31 +Int X) /Int 32 *Int 32 => #ceil32(X)

    rule #asWord(#buf(32, DATA)) => DATA  requires #rangeUInt(256, DATA)

    rule #padToWidth(32, #asByteStack(V)) => #buf(32, V) // #asByteStackInWidth(V, 32)
      requires 0 <=Int V andBool V <Int pow256 andBool #getKLabelString(V) =/=String "#asWord"

    rule #buf(32, #asWord(#bufSeg(BUF, START, WIDTH))) => #bufSeg(BUF, START +Int WIDTH -Int 32, 32)  requires WIDTH >=Int 32

    rule #asWord(#bufSeg(BUF, START, WIDTH)) &Int 255 => #asWord(#bufSeg(BUF, START +Int WIDTH -Int 1, 1))  requires WIDTH >=Int 1
    rule 255 &Int #asWord(#bufSeg(BUF, START, WIDTH)) => #asWord(#bufSeg(BUF, START +Int WIDTH -Int 1, 1))  requires WIDTH >=Int 1

    rule #bufSeg(BUF, START, 1) => #bufElm(BUF, START) : .WordStack
    rule #asWord(#bufElm(BUF, INDEX) : .WordStack) => #bufElm(BUF, INDEX)

    rule #buf(32, DATA) => #padToWidth(32, #asByteStack(DATA)) [concrete]

  // ########################
  // Arithmetic
  // ########################

    rule I1 +Int (A +Int I2) => A +Int (I1 +Int I2) when notBool #isConcrete(A) andBool #isConcrete(I1) andBool #isConcrete(I2)
    rule I1 +Int (I2 +Int A) => A +Int (I1 +Int I2) when notBool #isConcrete(A) andBool #isConcrete(I1) andBool #isConcrete(I2)

    rule (A +Int I1) +Int I2 => A +Int (I1 +Int I2) when notBool #isConcrete(A) andBool #isConcrete(I1) andBool #isConcrete(I2)
    rule (I1 +Int A) +Int I2 => A +Int (I1 +Int I2) when notBool #isConcrete(A) andBool #isConcrete(I1) andBool #isConcrete(I2)

    rule (A +Int I1) -Int I2 => A +Int (I1 -Int I2) when notBool #isConcrete(A) andBool #isConcrete(I1) andBool #isConcrete(I2)
    rule (I1 +Int A) -Int I2 => A +Int (I1 -Int I2) when notBool #isConcrete(A) andBool #isConcrete(I1) andBool #isConcrete(I2)

    rule (A +Int I1) +Int (I2 +Int B) => (A +Int B) +Int (I1 +Int I2) when notBool #isConcrete(A) andBool notBool #isConcrete(B) andBool #isConcrete(I1) andBool #isConcrete(I2)

    rule (A +Int I1) +Int (I2 -Int A) => I1 +Int I2
    rule (I1 +Int A) +Int (I2 -Int A) => I1 +Int I2

    rule (A +Int I1) -Int (A +Int I2) => I1 -Int I2
    rule (A +Int I1) -Int (I2 +Int A) => I1 -Int I2
    rule (I1 +Int A) -Int (A +Int I2) => I1 -Int I2
    rule (I1 +Int A) -Int (I2 +Int A) => I1 -Int I2

    // Simplify Cmem(_,_) - Cmem(_, _)
    rule A +Int (I1 -Int A) => I1
    rule (I1 +Int (A -Int I0)) +Int (I2 -Int A) => I1 +Int (I2 -Int I0)

    // 0xffff...f &Int N = N
    rule MASK &Int N => N  requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 // MASK = 0xffff...f
                            andBool 0 <=Int N andBool N <=Int MASK

    // N &Int 0xffff...f = N
    rule N &Int MASK => N  requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 // MASK = 0xffff...f
                            andBool 0 <=Int N andBool N <=Int MASK

    // TODO: move to builtin
    rule N -Int N => 0

    rule 2 ^%Int X pow256 => 2 ^Int X
      requires 0 <=Int X andBool X <Int 256

    rule X modInt Y => X
      requires 0 <=Int X andBool X <Int Y

    rule ((X *Int Y) /Int Z) /Int Y => X /Int Z
      requires Y =/=Int 0

    // 0xff..ff00..00 (16 1's followed by 240 0's)
    rule 115790322390251417039241401711187164934754157181743688420499462401711837020160 &Int #asWord(WS1 ++ WS2)
        => #asWord(WS1 ++ #buf(30, 0))
      requires #sizeWordStack(WS1) ==Int 2
       andBool #sizeWordStack(WS2) ==Int 30

endmodule
