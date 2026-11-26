# Running a compiled program agrees with the evaluator

Let `1 < q` and `enc` a permutation of `ZMod q`. For every program `p` and
input labels, `runProg enc inputs p` equals `eval (oracleOf enc) inputs p`.
