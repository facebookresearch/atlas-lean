# Queries issued along an evaluation path

Let `L` be a type of labels with decidable equality and `O : Query L → L` an
oracle answering multiplication and inversion queries. `queriesOf O env p`
lists the queries issued along the path that `eval O env p` takes: the same
recursion as `eval`, collecting each query instead of only answering it.
