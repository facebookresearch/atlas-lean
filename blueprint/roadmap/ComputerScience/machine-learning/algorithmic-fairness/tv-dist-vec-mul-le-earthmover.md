# Classifier-level earthmover bound

For a classifier `M` on a finite outcome set that is
individually fair with respect to a task metric `d` and probability distributions `S` and `T`
on a finite set of individuals (nonnegative entries summing to `1`), the total variation
distance between the induced outcome distributions `S ᵥ* Matrix.of M` and `T ᵥ* Matrix.of M`,
with entries `∑ x, S x * M x o` and `∑ x, T x * M x o`, is at most `earthmover d S T`, the
earthmover value of `S` and `T` for the same `d`.
