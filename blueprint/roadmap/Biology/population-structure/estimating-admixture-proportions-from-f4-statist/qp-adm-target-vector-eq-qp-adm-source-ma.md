# Weights of an affine source mixture solve the f4 linear system

Let `μ` be a measure on `Ω` and let the allele frequency `p X` of every population `X` be square
integrable. Let `T` be a target, `S 0, …, S k` sources and `R 0, …, R r` right populations, and let
`w 0, …, w k` be real weights of any sign with `w 0 + … + w k = 1` such that
`p T ω = ∑ l, w l * p (S l) ω` for every `ω`. Then the [target vector](qp-adm-target-vector.md) `b`
and the [source matrix](qp-adm-source-matrix.md) `A` satisfy `b j = ∑ l, A j l * w l`, the sum over
`1 ≤ l ≤ k`, for every `1 ≤ j ≤ r`: the weights `(w 1, …, w k)` of the non-reference sources solve
the linear system `A v = b` (Haak et al. 2015). The weight `w 0` of the reference source does not
enter.
