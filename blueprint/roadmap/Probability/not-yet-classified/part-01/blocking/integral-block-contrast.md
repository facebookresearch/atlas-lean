# Integral block Contrast

Weighted block contrast is unbiased for the population ATE.
Clause map: fixed pre-treatment partition (`blocks`, disjointness `hdisj`, coverage
`hcover`); independent complete randomization per block (`blockRandomization` with
treated counts `n`); per-block contrast of the treated-set coordinate as `diffInMeans`
(`blockContrast`); block-size weights (`(blocks b).card / N`); both arms in every block
(`h₁`, `h₀`).
