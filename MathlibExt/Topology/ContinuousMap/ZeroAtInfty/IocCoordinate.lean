/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# The coordinate function on a half-open interval

For every real endpoint `b`, the complex coordinate `x↦x` on `(0,b]`
is a continuous function vanishing at infinity. Its supremum norm is
`max(b,0)`. When `b≤0` the domain is empty and that norm is zero; no
positive-endpoint assumption is imposed.

The coordinate tends to zero along the interval's cocompact filter and
is a positive C-star-algebra element: it equals `star(g) * g` for a
vanishing-at-infinity function given by the nonnegative square root on
the same interval.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter
open scoped ZeroAtInfty

noncomputable section

namespace ZeroAtInftyContinuousMap

/-- The complex-valued coordinate function on `(0,b]`, including the empty domain when `b≤0`. -/
def iocCoordinate (b : ℝ) : C₀(Set.Ioc (0 : ℝ) b, ℂ) where
  toFun x := ((x : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp continuous_subtype_val
  zero_at_infty' := by
    apply Metric.tendsto_nhds.mpr
    intro epsilon hepsilon
    let K : Set (Set.Ioc (0 : ℝ) b) := {x | epsilon ≤ (x : ℝ)}
    have hK : IsCompact K := by
      apply Subtype.isCompact_iff.mpr
      have himage : Subtype.val '' K = Set.Icc epsilon b := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨hy, y.property.2⟩
        · intro hx
          exact ⟨⟨x, ⟨lt_of_lt_of_le hepsilon hx.1, hx.2⟩⟩, hx.1, rfl⟩
      rw [himage]
      exact isCompact_Icc
    filter_upwards [hK.compl_mem_cocompact] with x hx
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos x.property.1]
    exact not_le.mp hx

/-- The C0 coordinate has exactly the original real coordinate, embedded in the complex numbers.

```lean
theorem iocCoordinate_apply (b : ℝ) (x : Set.Ioc (0 : ℝ) b) :
    iocCoordinate b x = ((x : ℝ) : ℂ)
``` -/
@[simp]
theorem iocCoordinate_apply (b : ℝ) (x : Set.Ioc (0 : ℝ) b) :
    iocCoordinate b x = ((x : ℝ) : ℂ) := by
  rfl

/-- The coordinate tends to zero along the cocompact filter of `(0,b]`.

```lean
theorem iocCoordinate_zero_at_infty (b : ℝ) :
    Tendsto (fun x : Set.Ioc (0 : ℝ) b => ((x : ℝ) : ℂ))
      (cocompact (Set.Ioc (0 : ℝ) b)) (nhds 0)
``` -/
theorem iocCoordinate_zero_at_infty (b : ℝ) :
    Tendsto (fun x : Set.Ioc (0 : ℝ) b => ((x : ℝ) : ℂ))
      (cocompact (Set.Ioc (0 : ℝ) b)) (nhds 0) :=
  zero_at_infty (iocCoordinate b)

/-- The coordinate supremum norm is exactly `max(b,0)`.

```lean
theorem norm_iocCoordinate (b : ℝ) : ‖iocCoordinate b‖ = max b 0
``` -/
@[simp]
theorem norm_iocCoordinate (b : ℝ) : ‖iocCoordinate b‖ = max b 0 := by
  have hupper : ‖iocCoordinate b‖ ≤ max b 0 := by
    rw [← norm_toBCF_eq_norm]
    apply (BoundedContinuousFunction.norm_le (le_max_right b 0)).2
    intro x
    change ‖((x : ℝ) : ℂ)‖ ≤ max b 0
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos x.property.1]
    exact x.property.2.trans (le_max_left b 0)
  apply le_antisymm hupper
  by_cases hb : 0 < b
  · have hlower := (iocCoordinate b).toBCF.norm_coe_le_norm
      (⟨b, ⟨hb, le_rfl⟩⟩ : Set.Ioc (0 : ℝ) b)
    change ‖(b : ℂ)‖ ≤ ‖iocCoordinate b‖ at hlower
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb] at hlower
    simpa only [max_eq_left hb.le] using hlower
  · have hnonpos : b ≤ 0 := le_of_not_gt hb
    let : IsEmpty (Set.Ioc (0 : ℝ) b) :=
      ⟨fun x => (not_lt_of_ge hnonpos)
        (lt_of_lt_of_le x.property.1 x.property.2)⟩
    have hzero : iocCoordinate b = 0 := eq_of_empty _ _
    simpa only [hzero, norm_zero, max_eq_right hnonpos] using
      (le_rfl : (0 : ℝ) ≤ 0)

/-- A C0 square-root function on the same interval gives the coordinate as `star(g)*g`.

```lean
theorem iocCoordinate_eq_star_mul_self (b : ℝ) :
    ∃ g : C₀(Set.Ioc (0 : ℝ) b, ℂ), iocCoordinate b = star g * g
``` -/
theorem iocCoordinate_eq_star_mul_self (b : ℝ) :
    ∃ g : C₀(Set.Ioc (0 : ℝ) b, ℂ), iocCoordinate b = star g * g := by
  have hreal :
      Tendsto (fun x : Set.Ioc (0 : ℝ) b => (x : ℝ))
        (cocompact (Set.Ioc (0 : ℝ) b)) (nhds 0) :=
    Filter.tendsto_ofReal_iff.mp (iocCoordinate_zero_at_infty b)
  let g : C₀(Set.Ioc (0 : ℝ) b, ℂ) :=
    { toFun := fun x => (Real.sqrt (x : ℝ) : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp continuous_subtype_val)
      zero_at_infty' := by
        have hs := (Real.continuous_sqrt.tendsto 0).comp hreal
        have hc := (Complex.continuous_ofReal.tendsto (Real.sqrt 0)).comp hs
        simpa only [Function.comp_def, Real.sqrt_zero, Complex.ofReal_zero] using hc }
  refine ⟨g, ?_⟩
  ext x
  change ((x : ℝ) : ℂ) =
    star (Real.sqrt (x : ℝ) : ℂ) * (Real.sqrt (x : ℝ) : ℂ)
  rw [show star (Real.sqrt (x : ℝ) : ℂ) = (Real.sqrt (x : ℝ) : ℂ) by simp,
    ← Complex.ofReal_mul]
  exact congrArg (fun r : ℝ => (r : ℂ))
    (Real.mul_self_sqrt x.property.1.le).symm

end ZeroAtInftyContinuousMap
