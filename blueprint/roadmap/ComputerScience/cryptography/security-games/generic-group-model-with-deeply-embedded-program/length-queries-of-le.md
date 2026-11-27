# Evaluation issues at most numQueries queries

Let `L` be a type of labels with decidable equality and `O : Query L → L` an
oracle answering multiplication and inversion queries. For every environment
`env` and program `p`, the number of queries issued along the path that `eval
O env p` takes is at most `numQueries p`.
