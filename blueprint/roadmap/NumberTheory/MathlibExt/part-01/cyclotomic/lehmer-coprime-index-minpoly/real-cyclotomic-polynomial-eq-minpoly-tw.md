---
article_id: af_90fb7c978acca212e4ac112c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.realCyclotomicPolynomial_eq_minpoly_two_cos
---

# Real Cyclotomic Polynomial eq minpoly two cos

Minimal polynomial of `2 cos (2πk/n)` for `Nat.Coprime k n`:
it equals the real cyclotomic polynomial at `n` (for `2 < n`). No range hypothesis on `k` is
needed, since the cosine depends only on `k` modulo `n`.

## Depends on

- [Real Cyclotomic Polynomial](../real-cyclotomic-polynomial.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Cyclotomic.LehmerCoprimeIndexMinpoly](../../../../../../sources/v2/MathlibExt.md)
