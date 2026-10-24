---
article_id: af_2f9ec00b76ff42e9039c4022
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.kummer_congruence
---

# Kummer Congruence

Kummer's congruence for Bernoulli numbers (statement `kummer-congruence-s1`):
if `p` is prime and `m, n` are not divisible by `p - 1` with
`m ≡ n [MOD (p - 1) * p ^ t]`, then the modified Bernoulli quotients
`(1 - p ^ (m - 1)) * B m / m` and `(1 - p ^ (n - 1)) * B n / n` agree modulo
`p ^ (t + 1)`, stated as a `padicValRat` bound. The disjunction guards the
zero-difference case since `padicValRat p 0 = 0`.
See https://en.wikipedia.org/wiki/Kummer%27s_congruence.

Proof: We use Voronoi's finite-sum congruence in p-adic norm form, following
Ireland--Rosen, Ch. 15 §2, and Washington, Cor. 5.14, back to Kummer's 1851 paper.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Bernoulli.KummerCongruence](../../../../../sources/v2/MathlibExt.md)
- Ernst Eduard Kummer, "Über eine allgemeine Eigenschaft der rationalen Entwickelungscoefficienten einer bestimmten Gattung analytischer Functionen," Journal für die reine und angewandte Mathematik 41 (1851), 368–372, DOI 10.1515/crll.1851.41.368, https://doi.org/10.1515/crll.1851.41.368.
