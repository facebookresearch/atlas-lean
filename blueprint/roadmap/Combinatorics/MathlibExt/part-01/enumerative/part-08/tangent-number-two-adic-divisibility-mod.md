---
article_id: af_cc6aa9601a6d4224df508e36
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.tangentNumber_two_adic_divisibility_mod_six
---

# Tangent Number Divisibility

The signed tangent numbers, characterized by `T 0 = 0` and
`T (m+1) = [m = 0] − ∑_k C(m,k) T_k T_{m−k}` (the `tanh` exponential
generating function coefficients, unsigned A009006), satisfy the stated
2-adic divisibility and congruence: for `n ≥ 1`, `2^n ∣ T_{2n+1}` and
`T_{2n+1} / 2^n ≡ (−1)^n 4^{n−1} (mod 6)`. The source defines `T` via
`1 + tanh x`, which agrees with this recurrence at odd indices.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.TangentNumberDivisibility](../../../../../../sources/v2/MathlibExt.md)
- Kwang-Wu Chen, "An Interesting Lemma for Regular C-fractions," Journal of Integer Sequences 6 (2003), Article 03.4.8, Theorem (label `thm.4`), equation (label `eq.38`), lines 362–369 (tangent numbers defined at lines 351–360), https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen53.tex
