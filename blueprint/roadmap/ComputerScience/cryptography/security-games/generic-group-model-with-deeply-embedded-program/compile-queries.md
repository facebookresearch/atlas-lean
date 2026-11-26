# Query transcript of a compiled program

Let `L` be a type of labels with decidable equality and `O : Query L → L` an
oracle answering multiplication and inversion queries. For every environment
`env` and program `p`, the query transcript of `GProg.compile env p` run
against `O` equals `queriesOf O env p`.
