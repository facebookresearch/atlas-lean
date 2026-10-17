---
article_id: af_f848b890d37f36f2f495c182
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.tuenter_bernoulli_power_sum_identity
---

# Tuenter Bernoulli Power Sum

Tuenter's power-sum identity for Bernoulli numbers (equation (23) at `c = 0`).

At `c = 0` the Bernoulli polynomial `B_0(n)` is the Bernoulli number `Bₙ` and
the denominator is `b^n - a^n`. The power sums are pinned by
`(i+1) * σ_x(i) = B_{i+1}(x+1) - B_{i+1}` from line 325. Integer exponents
are used since `n - 1 - i` can be `-1`, guarded by the nonzero hypotheses.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Bernoulli.TuenterBernoulliPowerSum](../../../../../sources/v2/MathlibExt.md)
- Jitender Singh, *On an Arithmetic Convolution*, Journal of Integer Sequences 17 (2014), Article 14.6.7, Corollary with equation `eq23`, lines 339–344, identified there as Tuenter's identity at `c = 0`, line 348, <https://cs.uwaterloo.ca/journals/JIS/VOL17/Singh/singh8.tex>.
