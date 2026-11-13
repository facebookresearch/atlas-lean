# Posterior probability that the cancer cell fraction exceeds a threshold

Landau et al.'s posterior probability that the CCF exceeds `t`, given `a` of `n` reads,
purity `α`, copy number `q`, a prior `prior` on the grid points `grid k`:
`∑_{grid k > t} π_k Binom(a | n, f(grid k)) / ∑_k π_k Binom(a | n, f(grid k))`, with
`f(c) = α c / (α q + 2 (1 - α))`.
