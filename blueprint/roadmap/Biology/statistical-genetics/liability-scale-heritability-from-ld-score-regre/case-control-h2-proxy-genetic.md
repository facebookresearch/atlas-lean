# Closed form of the case-control proxy under the Gaussian model

Let `μ` be a probability measure on `Ω`, let `G` and `L` be real functions on `Ω` such that the pair
`(G, L)` has a Gaussian law under `μ` (it is `μ`-almost everywhere measurable and its law is a
Gaussian measure on `ℝ²`, possibly degenerate), let `L` be measurable with the standard normal law
under `μ`, and let `h²` be a real number with `Var G = h²` and `Cov(G, L) = h²`, and let
`0 < P < 1`. Then for every real threshold `t`, the
[case-control heritability proxy](case-control-h2-proxy.md) with case fraction `P` is

`h²_cc = h² P (1 - P) z² / (K² (1 - K)²)`,

with the [prevalence](prevalence.md) `K = K(t)` and the
[standard normal density at the threshold](threshold-density.md) `z = z(t)`.
