---
article_id: af_cfc841da128aee1efe47431e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.eulerMaclaurinFormula
---

# Euler Maclaurin Formula

Euler-Maclaurin formula (canonical name "Euler-Maclaurin formula",
statement `euler-maclaurin-s1`).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Calculus.EulerMaclaurinFormula](../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Euler%E2%80%93Maclaurin_formula. Let `f` be `p`-times continuously differentiable on `[a, b]` with integers `a < b`, and `B_{2k}` the Bernoulli numbers. Then `∑ n ∈ Icc a b, f n` equals `∫ x in a..b, f x + (f a + f b) / 2` plus `∑ k ∈ Icc 1 (p / 2), B_{2k} / (2k)! * (f^{(2k-1)} b - f^{(2k-1)} a)` plus the standard periodic-Bernoulli remainder integral `(-1)^(p+1) / p! ∫ x in a..b, P_p x * f^{(p)} x`, where `P_p` is the `1`-periodic Bernoulli kernel agreeing on the half-open interval `[0, 1)` with the Bernoulli polynomial `∑ j ∈ range (p+1), C(p,j) B_j x^(p-j)` under the standard `B_1 = -1/2` convention.
