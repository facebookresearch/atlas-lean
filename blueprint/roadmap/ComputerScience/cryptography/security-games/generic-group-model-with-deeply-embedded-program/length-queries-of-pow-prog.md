# The exponentiation program issues exactly m queries

Let `L` be a type of labels with decidable equality and `O : Query L → L` an
oracle answering multiplication and inversion queries. For every environment
`env : Fin 2 → L`, the exponentiation program `powProg m` issues exactly `m`
queries along its evaluation path.
