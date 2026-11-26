# Distinct fresh queries get independent uniform answers

Let the domain `D` have decidable equality and the range `Rng` be finite and
nonempty. If the points `xs : Fin n → D` are pairwise distinct and none is
recorded in the table `T`, then querying them in order from a lazily sampled
random oracle with table `T` yields a uniformly random answer vector `Fin n →
Rng`.
