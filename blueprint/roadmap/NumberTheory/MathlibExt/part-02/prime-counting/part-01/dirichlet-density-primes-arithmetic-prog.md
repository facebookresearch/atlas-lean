---
article_id: af_127e089a4ce041b944d574a6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.NumberTheory.PrimeCounting.dirichlet_density_primes_arithmetic_progression
---

# Dirichlet Density Arithmetic Progression

For `0 < m` and `Nat.Coprime a m`, the relative Dirichlet density over natural
residue representatives of the primes `p ≡ a [MOD m]` equals `1 / φ(m)`: as real
`s → 1⁺`, the quotient of the prime reciprocal-power sums tends to `1 / φ(m)`.

This is a different target from `Chebyshev.weakPNT_arithmeticProgression`, which is
a von-Mangoldt Cesàro limit rather than this Dirichlet-density formula.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeCounting.DirichletDensityArithmeticProgression](../../../../../../sources/v2/MathlibExt.md)
- B. Li, S. J. Miller, T. Popescu, D. Sarnecki, and N. Wattanawanichkul, "Modeling Random Walks to Infinity on Primes in Z[sqrt(2)]", *Journal of Integer Sequences* 25 (2022), Article 22.6.1, [TeX source](https://cs.uwaterloo.ca/journals/JIS/VOL25/Miller/miller11.tex), relative Dirichlet-density definition at lines 281-285 and primes-in-arithmetic- progressions statement at lines 290-292.
