---
article_id: af_84d22511ecdc975ab96fb201
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.genocchiNumber_eq_stirlingSecond_sum_general
---

# Genocchi Number eq stirling Second sum general

Garabedian's explicit formula for the Genocchi numbers, for every `n : ℕ`:
`G n = n * ∑ k = 1..n, (-1)^(n-k) * (k-1)! * S(n, k) / 2^(k-1)`. At `n = 0` both sides are `0`.
`genocchiNumber_eq_stirlingSecond_sum` is the source-shaped form.

## Depends on

- [Genocchi Number](../../../../../../NumberTheory/MathlibExt/part-06/genocchi-number/genocchi-number.md)

## Proof depends on

- [Garabedian genocchi formula general](../garabedian-bernoulli-stirling/garabedian-genocchi-formula-general.md)
- [Genocchi Number eq bernoulli](../../../../../../NumberTheory/MathlibExt/part-06/genocchi-bernoulli/genocchi-number-eq-bernoulli.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.GarabedianGenocchiFormula](../../../../../../../sources/v2/MathlibExt.md)
