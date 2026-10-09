---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CDIS.map_boxMuller, CDIS.hasLaw_boxMuller, CDIS.boxMuller_gaussian
---

# Box-Muller transform

CDIS id 98. If `U, V` are independent and uniform on `]0,1[`, then
 `X = √(-2 ln U) cos(2πV)` and `Y = √(-2 ln U) sin(2πV)` are independent standard normal
 variables. Proof: the map `(r, θ) ↦ (e^{-r²/2}, (θ + π) / 2π)` sends `]0,∞[ × ]-π,π[`
 onto `]0,1[²` with Jacobian `r e^{-r²/2} / 2π`. Mathlib's polar coordinates take
 `θ ∈ ]-π,π[`, and since `cos(θ + π) = -cos θ` and `sin(θ + π) = -sin θ`, the Box-Muller map
 becomes `-polarCoord.symm` (`CDIS.boxMuller_subst`). `lintegral_comp_polarCoord_symm` then
 identifies the law with the image of the standard Gaussian on `ℝ²` under `x ↦ -x`, which is
 the standard Gaussian again. No earlier public Lean
 proof was found (sosudo/ppl-pralean states it with `sorry`).

## Depends on

No prerequisite in this chapter.

## Sources

- [Probabilités V, Box-Muller](../../sources/cdis-probabilites-v.md)
