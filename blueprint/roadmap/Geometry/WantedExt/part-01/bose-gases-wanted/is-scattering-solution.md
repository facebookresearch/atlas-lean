---
article_id: af_2cb95e08e56882d4f27813ed
declaration: structure
origin: cited
statement: formalized
lean: MathlibExt.Geometry.BoseGasesWanted.BoseGases.IsScatteringSolution
---

# Is Scattering Solution

We say that `w : ℝ³ → ℝ` is a scattering solution to the scattering equation with potential
`v` if `w` is locally integrable, `w x → 0` as `|x| → ∞`, and `w` satisfies the equation:

`- Δ w = 1/2 v (1 - w)` (Equation (3.4) in the paper)

in the weak sense that `w, v(1 - w) ∈ L¹_loc (ℝ³)` and for any `φ ∈ C∞c(ℝ³)`

`- ∫ w * (Δ φ) = (1 / 2) * ∫ v * (1 - w) * φ`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Geometry.BoseGasesWanted](../../../../../sources/v2/WantedExt.md)
