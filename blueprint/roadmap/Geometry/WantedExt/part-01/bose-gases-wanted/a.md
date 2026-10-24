---
article_id: af_18c6f8e53ffbd2534357a4a3
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Geometry.BoseGasesWanted.BoseGases.a
---

# A

When the potential `v : ℝ³ → ℝ` has a radial scattering solution `w : ℝ³ → ℝ`, we define
the scattering length `a` of `v` (using Equation (3.5)) by

`a = (8 π)⁻¹ ∫ v * (1 - w)`.

Under the assumptions of theorem 1.2 we know that `v` has a unique radial scattering solution,
and hence a well-defined scattering length `a`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Radial](is-radial.md)
- [Is Scattering Solution](is-scattering-solution.md)

## Sources

- [WantedExt, WantedExt.Geometry.BoseGasesWanted](../../../../../sources/v2/WantedExt.md)
