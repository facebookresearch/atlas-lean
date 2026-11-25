# Running a compiled program agrees with the evaluator

Let `L` be a type of labels with decidable equality and `O : Query L → L` an
oracle answering multiplication and inversion queries. For every environment
`env` and program `p`, running `GProg.compile env p` against `O` returns `eval
O env p`.
