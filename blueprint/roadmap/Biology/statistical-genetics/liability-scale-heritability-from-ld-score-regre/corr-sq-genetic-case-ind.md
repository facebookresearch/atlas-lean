# Dempster–Lerner formula for the observed-scale heritability

Let `μ` be a probability measure on `Ω`, let `G` and `L` be real functions on `Ω` such that the pair
`(G, L)` has a Gaussian law under `μ` (it is `μ`-almost everywhere measurable and its law is a
Gaussian measure on `ℝ²`, possibly degenerate), let `L` be measurable with the standard normal law
under `μ`, and let `h²` be a real number with `Var G = h²` and `Cov(G, L) = h²`, as in the liability
model `L = G + E` with `E` independent of `G`
([joint Gaussianity](has-gaussian-law-liability.md), [covariance](covariance-liability.md)). Then for every real threshold `t`, with the [case indicator](case-ind.md) `Y = 1{L ≥ t}`, the observed-scale heritability `h²_o = corr²(G, Y)` ([squared correlation](corr-sq.md)) is

`h²_o = h² z² / (K (1 - K))`,

with the [prevalence](prevalence.md) `K = K(t)` and the
[standard normal density at the threshold](threshold-density.md) `z = z(t)`. The formula of Dempster
and Lerner (1950) is thus exact under this Gaussian model. For `h² = 0` both sides are `0`, the left
by the convention `x / 0 = 0`.
