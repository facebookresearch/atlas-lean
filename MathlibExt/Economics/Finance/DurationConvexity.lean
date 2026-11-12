/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.Slope

/-!
# Duration, convexity, and the tangent-line approximation

For fixed nonnegative cash flows, the bond price
`bondPrice c s r = ∑ t ∈ s, c t * (1 + r) ^ (-t)` is convex in the yield on
`(-1, ∞)` and differentiable there, so it lies above its tangent line at any
base yield (`bondPrice_ge_tangent`). The tangent slope is
`deriv (bondPrice c s) r₀`; once the FI04.T01 identity is unified with this
file, the slope reads `-Dmod(r₀) * P(r₀)` for the modified duration.

## Main results

* `MathlibExt.Economics.Finance.DurationConvexity.convexOn_bondPrice`
* `MathlibExt.Economics.Finance.DurationConvexity.hasDerivAt_bondPrice`
* `MathlibExt.Economics.Finance.DurationConvexity.bondPrice_ge_tangent`

## References

OpenStax, *Principles of Finance*, bonds and interest rates; SOA Exam FM
syllabus (duration and convexity). Atlas roadmap target FI04.T02.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.DurationConvexity

/-- Price at yield `r` of the fixed cash flows `c t` paid at dates `t ∈ s`:
`∑ t ∈ s, c t * (1 + r) ^ (-t)`. Meaningful for `r > -1`. -/
noncomputable def bondPrice (c : ℕ → ℝ) (s : Finset ℕ) (r : ℝ) : ℝ :=
  ∑ t ∈ s, c t * (1 + r) ^ (-(t : ℤ))

/-- The affine shift `r ↦ 1 + r`. -/
private def shift1 : ℝ →ᵃ[ℝ] ℝ where
  toFun := fun r => 1 + r
  linear := LinearMap.id
  map_vadd' := fun p v => by simp only [vadd_eq_add, LinearMap.id_apply]; ring

@[simp]
private theorem shift1_apply (r : ℝ) : shift1 r = 1 + r := rfl

private theorem shift1_preimage : ⇑shift1 ⁻¹' Set.Ioi 0 = Set.Ioi (-1) := by
  ext r
  simp only [Set.mem_preimage, Set.mem_Ioi, shift1_apply]
  constructor <;> intro h <;> linarith

/-- Each summand is convex on `(-1, ∞)` for nonnegative cash flows. -/
private theorem convexOn_term (c : ℕ → ℝ) (t : ℕ) (hct : 0 ≤ c t) :
    ConvexOn ℝ (Set.Ioi (-1)) (fun r => c t * (1 + r) ^ (-(t : ℤ))) := by
  have h1 : ConvexOn ℝ (⇑shift1 ⁻¹' Set.Ioi 0) ((fun x => x ^ (-(t : ℤ))) ∘ ⇑shift1) :=
    (convexOn_zpow _).comp_affineMap shift1
  rw [shift1_preimage] at h1
  have h2 := ConvexOn.smul hct h1
  simpa [smul_eq_mul, Function.comp_apply, shift1_apply] using h2

/-- Each summand is differentiable at any yield above `-1`. -/
private theorem hasDerivAt_term (c : ℕ → ℝ) (t : ℕ) (r₀ : ℝ) (hr₀ : -1 < r₀) :
    HasDerivAt (fun r => c t * (1 + r) ^ (-(t : ℤ)))
      (c t * (↑(-(t : ℤ)) * (1 + r₀) ^ (-(t : ℤ) - 1) * 1)) r₀ := by
  have hne : (1 : ℝ) + r₀ ≠ 0 := ne_of_gt (by linarith)
  have houter : HasDerivAt (fun x : ℝ => x ^ (-(t : ℤ)))
      (↑(-(t : ℤ)) * (1 + r₀) ^ (-(t : ℤ) - 1)) (1 + r₀) :=
    hasDerivAt_zpow (-(t : ℤ)) _ (Or.inl hne)
  have hinner : HasDerivAt (fun r : ℝ => 1 + r) 1 r₀ :=
    HasDerivAt.const_add 1 (hasDerivAt_id r₀)
  have hcomp : HasDerivAt (fun r : ℝ => (1 + r) ^ (-(t : ℤ)))
      ((↑(-(t : ℤ)) * (1 + r₀) ^ (-(t : ℤ) - 1)) * 1) r₀ :=
    HasDerivAt.comp r₀ houter hinner
  exact HasDerivAt.const_mul (c t) hcomp

/-- The bond price is differentiable at any yield above `-1`. -/
theorem hasDerivAt_bondPrice {c : ℕ → ℝ} {s : Finset ℕ} {r₀ : ℝ} (hr₀ : -1 < r₀) :
    HasDerivAt (bondPrice c s)
      (∑ t ∈ s, c t * (↑(-(t : ℤ)) * (1 + r₀) ^ (-(t : ℤ) - 1) * 1)) r₀ := by
  have hterm : ∀ t ∈ s, HasDerivAt (fun r => c t * (1 + r) ^ (-(t : ℤ)))
      (c t * (↑(-(t : ℤ)) * (1 + r₀) ^ (-(t : ℤ) - 1) * 1)) r₀ :=
    fun t _ => hasDerivAt_term c t r₀ hr₀
  exact HasDerivAt.fun_sum hterm

/-- The bond price is convex in the yield on `(-1, ∞)` when all cash flows are
nonnegative. -/
theorem convexOn_bondPrice {c : ℕ → ℝ} {s : Finset ℕ} (hc : ∀ t ∈ s, 0 ≤ c t) :
    ConvexOn ℝ (Set.Ioi (-1)) (bondPrice c s) := by
  revert hc
  refine Finset.induction_on s ?_ ?_
  · intro _
    have hempty : bondPrice c ∅ = fun _ => (0 : ℝ) := by
      funext r
      simp only [bondPrice, Finset.sum_empty]
    rw [hempty]
    exact convexOn_const 0 (convex_Ioi _)
  · intro a s has ih hc
    have hc'a : 0 ≤ c a := hc a (Finset.mem_insert_self a s)
    have hcs : ∀ t ∈ s, 0 ≤ c t := fun t ht => hc t (Finset.mem_insert_of_mem ht)
    have h1 : ConvexOn ℝ (Set.Ioi (-1)) (fun r => c a * (1 + r) ^ (-(a : ℤ))) :=
      convexOn_term c a hc'a
    have h2 : ConvexOn ℝ (Set.Ioi (-1)) (bondPrice c s) := ih hcs
    have hsum : bondPrice c (insert a s)
        = (fun r => c a * (1 + r) ^ (-(a : ℤ))) + bondPrice c s := by
      funext r
      simp only [bondPrice, Finset.sum_insert has, Pi.add_apply]
    rw [hsum]
    exact h1.add h2

/-- **Convexity beats the tangent-line duration approximation.** At any two yields
above `-1`, the true price lies above the tangent line at `r₀` (whose slope is
`deriv (bondPrice c s) r₀`; once FI04.T01 is unified with this file, the slope
reads `-Dmod(r₀) * P(r₀)` for the modified duration). -/
theorem bondPrice_ge_tangent {c : ℕ → ℝ} {s : Finset ℕ} (hc : ∀ t ∈ s, 0 ≤ c t)
    {r₀ r : ℝ} (hr₀ : -1 < r₀) (hr : -1 < r) :
    bondPrice c s r ≥ bondPrice c s r₀ + deriv (bondPrice c s) r₀ * (r - r₀) := by
  have hconv : ConvexOn ℝ (Set.Ioi (-1)) (bondPrice c s) := convexOn_bondPrice hc
  have hderiv : HasDerivAt (bondPrice c s) _ r₀ := hasDerivAt_bondPrice hr₀
  rw [hderiv.deriv]
  have hmem0 : r₀ ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr hr₀
  have hmem : r ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr hr
  rcases lt_trichotomy r r₀ with hlt | heq | hgt
  · have hslope := hconv.slope_le_of_hasDerivAt hmem hmem0 hlt hderiv
    rw [slope_def_field] at hslope
    have hpos : (0 : ℝ) < r₀ - r := by linarith
    have hmul := (div_le_iff₀ hpos).mp hslope
    linarith
  · subst heq
    simp only [sub_self, mul_zero, add_zero, le_refl]
  · have hslope := hconv.le_slope_of_hasDerivAt hmem0 hmem hgt hderiv
    rw [slope_def_field] at hslope
    have hpos : (0 : ℝ) < r - r₀ := by linarith
    have hmul := (le_div_iff₀ hpos).mp hslope
    linarith

end MathlibExt.Economics.Finance.DurationConvexity
