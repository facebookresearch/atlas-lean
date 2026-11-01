---
article_id: af_1ceef7eb409de9a07d9b0606
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.kurosaki_phi_pow_power_free
---

# Kurosaki Power Free

For alphabet {1,2,3}, with σ swapping 1 and 2, ρ swapping 2 and 3,
and φ(a) = σ(a) a ρ(a), every iterate φ^n(2) with n ≥ 1 has every
factor of exponent at most 7/4.

Letters 1, 2, 3 are encoded as `Fin 3` values 0, 1, 2; the
`(7/4)+`-power-free conclusion is rendered as `4 * length ≤ 7 * p`
for every factor with period `p`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Words.KurosakiPowerFree](../../../../../sources/v2/MathlibExt.md)
- Serina Camungol and Narad Rampersad, "Concerning Kurosaki's Squarefree Word," Journal of Integer Sequences 16 (2013), Article 13.9.4, Theorem (label 7/4powerfree), lines 184–188, with the σ/ρ/φ definitions at lines 116–124, https://cs.uwaterloo.ca/journals/JIS/VOL16/Camungol/ramper4.tex
