# Case-control conversion of Lee et al. to the liability scale

Let `μ` be a probability measure on `Ω`, let `G` and `L` be real functions on `Ω` such that the pair
`(G, L)` has a Gaussian law under `μ` (it is `μ`-almost everywhere measurable and its law is a
Gaussian measure on `ℝ²`, possibly degenerate), let `L` be measurable with the standard normal law
under `μ`, and let `h²` be a real number with `Var G = h²` and `Cov(G, L) = h²`, and let
`0 < P < 1`. Then for every real threshold `t`,

`h² = (K² (1 - K)² / (P (1 - P) z²)) · h²_cc`:

the liability-scale heritability is the [case-control conversion factor](cc-liability-factor.md) of
Lee, Wray, Goddard and Visscher (2011) times the
[case-control heritability proxy](case-control-h2-proxy.md) `h²_cc` with case fraction `P`, with the
[prevalence](prevalence.md) `K = K(t)` and the
[standard normal density at the threshold](threshold-density.md) `z = z(t)`.
