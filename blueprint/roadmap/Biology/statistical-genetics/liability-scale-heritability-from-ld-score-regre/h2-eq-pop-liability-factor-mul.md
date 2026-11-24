# Dempster–Lerner conversion from the observed to the liability scale

Let `μ` be a probability measure on `Ω`, let `G` and `L` be real functions on `Ω` such that the pair
`(G, L)` has a Gaussian law under `μ` (it is `μ`-almost everywhere measurable and its law is a
Gaussian measure on `ℝ²`, possibly degenerate), let `L` be measurable with the standard normal law
under `μ`, and let `h²` be a real number with `Var G = h²` and `Cov(G, L) = h²`. Then for every real
threshold `t`, with the [case indicator](case-ind.md) `Y = 1{L ≥ t}`,

`h² = (K (1 - K) / z²) · corr²(G, Y)`:

the liability-scale heritability is the [population conversion factor](pop-liability-factor.md)
times the observed-scale heritability, the [squared correlation](corr-sq.md) of `G` and `Y`, with
the [prevalence](prevalence.md) `K = K(t)` and the
[standard normal density at the threshold](threshold-density.md) `z = z(t)`.
