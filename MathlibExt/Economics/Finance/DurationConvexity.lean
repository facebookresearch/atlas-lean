/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.DatedCashFlow
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.Slope

/-!
# Duration, convexity, and the tangent-line approximation

For fixed nonnegative cash flows `c` paid at the dates `s`, the constant-rate
present value `presentValue (discountFactor r) s c = ∑ t ∈ s, ((1 + r) ^ t)⁻¹ * c t`
of `MathlibExt.Economics.Finance.DatedCashFlow` is convex in the yield `r` on
`(-1, ∞)` and differentiable there, so it lies above its tangent line at any base
yield (`presentValue_discountFactor_ge_tangent`). The tangent slope is
`-presentValue (discountFactor r₀) s (fun t => t * c t) / (1 + r₀)`
(`hasDerivAt_presentValue_discountFactor`); divided by minus the price it is the
modified duration, so the tangent line is the first-order duration approximation.

## Main results

* `MathlibExt.Economics.Finance.DurationConvexity.convexOn_presentValue_discountFactor`
* `MathlibExt.Economics.Finance.DurationConvexity.hasDerivAt_presentValue_discountFactor`
* `MathlibExt.Economics.Finance.DurationConvexity.presentValue_discountFactor_ge_tangent`

## References

OpenStax, *Principles of Finance*, bonds and interest rates; SOA Exam FM
syllabus (duration and convexity). Atlas roadmap target FI04.T02.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.DurationConvexity

/-- The constant-rate present value in negative-power form:
`((1 + r) ^ t)⁻¹ * c t = c t * (1 + r) ^ (-t)`. -/
private theorem presentValue_discountFactor_eq_zpow (c : ℕ → ℝ) (s : Finset ℕ) :
    (fun r => presentValue (discountFactor r) s c) =
      fun r => ∑ t ∈ s, c t * (1 + r) ^ (-(t : ℤ)) := by
  funext r
  unfold presentValue discountFactor
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [zpow_neg, zpow_natCast, mul_comm]

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

/-- The constant-rate present value is differentiable in the yield at any `r₀ > -1`,
with derivative `-presentValue (discountFactor r₀) s (fun t => t * c t) / (1 + r₀)`. -/
theorem hasDerivAt_presentValue_discountFactor {c : ℕ → ℝ} {s : Finset ℕ} {r₀ : ℝ}
    (hr₀ : -1 < r₀) :
    HasDerivAt (fun r => presentValue (discountFactor r) s c)
      (-presentValue (discountFactor r₀) s (fun t => (t : ℝ) * c t) / (1 + r₀)) r₀ := by
  have hne : (1 : ℝ) + r₀ ≠ 0 := ne_of_gt (by linarith)
  rw [presentValue_discountFactor_eq_zpow c s]
  refine (HasDerivAt.fun_sum fun t _ => hasDerivAt_term c t r₀ hr₀).congr_deriv ?_
  simp only [presentValue, discountFactor]
  rw [neg_div, div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hexp : -(t : ℤ) - 1 = -((t + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hexp, zpow_neg, zpow_natCast, pow_succ]
  push_cast
  field_simp

/-- The constant-rate present value is convex in the yield on `(-1, ∞)` when all cash
flows are nonnegative. -/
theorem convexOn_presentValue_discountFactor {c : ℕ → ℝ} {s : Finset ℕ}
    (hc : ∀ t ∈ s, 0 ≤ c t) :
    ConvexOn ℝ (Set.Ioi (-1)) (fun r => presentValue (discountFactor r) s c) := by
  rw [presentValue_discountFactor_eq_zpow c s]
  revert hc
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact convexOn_const 0 (convex_Ioi _)
  · intro a s has ih hc
    have h1 : ConvexOn ℝ (Set.Ioi (-1)) (fun r => c a * (1 + r) ^ (-(a : ℤ))) :=
      convexOn_term c a (hc a (Finset.mem_insert_self a s))
    have h2 := ih fun t ht => hc t (Finset.mem_insert_of_mem ht)
    have hsum : (fun r => ∑ t ∈ insert a s, c t * (1 + r) ^ (-(t : ℤ)))
        = (fun r => c a * (1 + r) ^ (-(a : ℤ))) +
          fun r => ∑ t ∈ s, c t * (1 + r) ^ (-(t : ℤ)) := by
      funext r
      simp only [Finset.sum_insert has, Pi.add_apply]
    rw [hsum]
    exact h1.add h2

/-- **Convexity beats the tangent-line duration approximation.** At any two yields
above `-1`, the constant-rate present value of nonnegative cash flows lies above its
tangent line at `r₀`, whose slope is computed in
`hasDerivAt_presentValue_discountFactor`. -/
theorem presentValue_discountFactor_ge_tangent {c : ℕ → ℝ} {s : Finset ℕ}
    (hc : ∀ t ∈ s, 0 ≤ c t) {r₀ r : ℝ} (hr₀ : -1 < r₀) (hr : -1 < r) :
    presentValue (discountFactor r) s c ≥
      presentValue (discountFactor r₀) s c +
        deriv (fun x => presentValue (discountFactor x) s c) r₀ * (r - r₀) := by
  have hconv := convexOn_presentValue_discountFactor hc
  have hderiv : HasDerivAt (fun x => presentValue (discountFactor x) s c)
      (deriv (fun x => presentValue (discountFactor x) s c) r₀) r₀ :=
    (hasDerivAt_presentValue_discountFactor hr₀).differentiableAt.hasDerivAt
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
