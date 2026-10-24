---
article_id: af_a02c4db551275772545e7146
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.rational_parametrization_pow_swap
---

# Rational Parametrization Pow Swap

Rational parametrization of `x ^ y = y ^ x` (Bernoulli/Hurwitz).

Every pair of positive rationals `y < x` with `(x : ℝ) ^ (y : ℝ) =
(y : ℝ) ^ (x : ℝ)` (real powers) is `x = (1 + 1/v)^(v+1)`,
`y = (1 + 1/v)^v` for some positive `v : ℕ`; the source states `v ∈ ℕ`
and `1/v` forces `v ≥ 1`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.RationalParametrizationPowSwap](../../../../sources/v2/MathlibExt.md)
- Hirotaka Kobayashi, Kota Saito, and Wataru Takeda, "Transcendence of Values of the Iterated Exponential Function at Algebraic Points," Journal of Integer Sequences 26 (2023), Article 23.3.3, Lemma (label x^y=y^x), lines 579–589, https://cs.uwaterloo.ca/journals/JIS/VOL26/Takeda/tak6.tex quoting Hurwitz. Proves `Wanted` entry `rational_parametrization_pow_swap`.
