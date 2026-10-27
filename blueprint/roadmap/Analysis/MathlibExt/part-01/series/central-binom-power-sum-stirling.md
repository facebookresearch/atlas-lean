---
article_id: af_1ac25e9d5909853aa26068e6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.central_binom_power_sum_stirling
---

# Central Binom Power Sum

Central binomial power-sum identity via Stirling numbers of the second kind:
for every `m` and `|x| < 1/4`,
`∑' n, C(2n,n) n^m x^n`
  `= (1 - 4x)^{-1/2} ∑_{k=0}^m S(m,k) C(2k,k) k! (x/(1-4x))^k`.

`S(m,k)` is `Nat.stirlingSecond m k` and the left side is a `tsum` over `ℕ`.
The source asks for positive `m`; the identity also holds at `m = 0`, where
both sides are the central binomial generating function.
Proves `Wanted` entry `central_binom_power_sum_stirling`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Series.CentralBinomPowerSum](../../../../../sources/v2/MathlibExt.md)
- Khristo N. Boyadzhiev, "Series with Central Binomial Coefficients, Catalan Numbers, and Harmonic Numbers," Journal of Integer Sequences 15 (2012), Article 12.1.7, Theorem (label t3, equation 8), lines 155–160, https://cs.uwaterloo.ca/journals/JIS/VOL15/Boyadzhiev/boyadzhiev6.tex
