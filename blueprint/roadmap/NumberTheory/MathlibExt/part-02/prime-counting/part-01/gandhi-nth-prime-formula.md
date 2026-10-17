---
article_id: af_80a8087c614c587808f7b699
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.PrimeCounting.GandhiNthPrimeFormulaWanted.gandhi_nthPrimeFormula
---

# Gandhi Nth Prime Formula

Gandhi's formula for the `n`th prime.

For one-indexed `n`, with `pᵢ` the `i`th prime and
`Pₙ₋₁ = p₁ * p₂ * ⋯ * pₙ₋₁` (the empty product `1` when `n = 1`),
`pₙ = ⌊1 - log₂(-1 / 2 + ∑_{d ∣ Pₙ₋₁} μ(d) / (2 ^ d - 1))⌋`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeCounting.GandhiNthPrimeFormula](../../../../../../sources/v2/MathlibExt.md)
- J. M. Gandhi, "Formulae for the nth prime," Proc. Washington State University Conference on Number Theory (1971), 96--107. The displayed formula and indexing follow the secondary source Eric S. Rowland, "A Natural Prime-Generating Recurrence," Journal of Integer Sequences 11 (2008), Article 08.2.8, lines 90--103 of the official TeX, https://cs.uwaterloo.ca/journals/JIS/VOL11/Rowland/rowland21.tex, where `f(n)` is the `n`th prime `pₙ` and `Pₙ = p₁ p₂ ⋯ pₙ`. Proves `Wanted` entry `gandhi_nthPrimeFormula`.
