# Classifier-level earthmover bound

For an individually fair classifier `M` and
probability distributions `S` and `T` on a finite set of individuals (nonnegative entries
summing to `1`), the total variation distance between the induced outcome distributions
`S ᵥ* Matrix.of M` and `T ᵥ* Matrix.of M`, with entries `∑ x, S x * M x o` and
`∑ x, T x * M x o`, is at most the earthmover value of `S` and `T` for the task
metric `d`.
