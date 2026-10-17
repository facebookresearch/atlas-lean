---
article_id: af_acf668978487c00b5db833e6
declaration: structure
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.GoodLTCodesWanted.GoodLTC.LTC
---

# LTC

A binary code `C ⊆ (𝔽₂)ⁿ` is `κ`-locally testable with `q` queries if there is a distribution
over a collection of `q`-element (or less) subsets `S ⊆ Fin n` such that each subset `S` is
associated with a set `V_S ⊆ 𝔽₂^S` of allowed local views, and such that the following hold:
* If `f ∈ C` then for every `S`, `f|_S ∈ V_S`.
* For every `f ∈ (𝔽₂)ⁿ`, `ℙ_S[f|_S ∉ V_S] ≥ κ * dist(f, C)`.

This is Definition 2.3 in `Locally Testable Codes with constant rate, distance, and locality` by
the same authors. This probability distribution formulation is also mentioned immediately after
Definition 1.1 in the original paper `Good Locally Testable Codes`.

## Depends on

- [Binary Code](binary-code.md)

## Sources

- [WantedExt, WantedExt.Combinatorics.GoodLTCodesWanted](../../../../../sources/v2/WantedExt.md)
