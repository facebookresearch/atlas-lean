---
article_id: af_7172d6fbff3c4890b3cfaf45
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.dobinski_formula_hasSum
---

# Dobinski Bell

Dobinski's formula for Bell numbers: for every `n : Nat`, including `n = 0`,
the real series with summand `(k : Real)^n / (k.factorial : Real)` indexed by
`k : Nat` from `k = 0` satisfies `HasSum` with value `Real.exp 1 * (Nat.bell n : Real)`,
so dividing by `Real.exp 1` gives the usual `1 / e` form. At `n = 0` and
`k = 0`, Lean's `0 ^ 0 = 1` is used, matching the exponential series.

Concept ID: `jis_dep_b5aac440aefd6e0d2de97890`.
Grounded record ID: `jis_grounded_f1b5718dcb195df798f06188`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.DobinskiBell](../../../../sources/v2/MathlibExt.md)
- `https://cs.uwaterloo.ca/journals/JIS/VOL14/Mezo/mezo9.tex`, lines 283-293. Source file SHA-256: `dbddfbb43d2055fbdcfac511e341bda8ef2def13cb9d80ddd429b75ed1b02927`. Source-text SHA-256: `f0df8e7588fe5cb6ca545ee2ce6973ea9dd1ffd15da7e303c1dadc9bc7d28a38`. Corrected classical accounting: 2 mentions / 2 papers / 0 proof uses (2/2/0). Only the classical Bell-number identity is stated here; the r-Bell generalizations are excluded.
