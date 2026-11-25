# Evaluating a generic-group program against an oracle

Let `L` be a type of labels with decidable equality and `O : Query L → L` an
oracle answering multiplication and inversion queries. `eval O env p` runs
program `p` in environment `env`: `ret i` returns `env i`; `mul` and `inv`
extend the environment with the oracle's answer to the corresponding query and
continue; `eqTest i j kt kf` continues with `kt` if `env i = env j` and with
`kf` otherwise. The definition is by structural recursion, so evaluation
always terminates.
