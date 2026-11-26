# The exponentiation recursion issues exactly m queries

Let `L` be a type of labels with decidable equality and `O : Query L → L` an
oracle answering multiplication and inversion queries. For every environment
`env` and indices `acc` and `base`, the exponentiation recursion `powProgAux m
acc base` issues exactly `m` queries along its evaluation path.
