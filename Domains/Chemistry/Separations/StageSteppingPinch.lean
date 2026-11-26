/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Monotone.Defs

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stage stepping cannot cross a pinch

The equilibrium curve and operating line are those of Lamm and Jarboe,
*Chemical Engineering Separations: A Handbook for Students*, §1.5, equations 22.2 and 20.7.
The result concerns only the order of the finite iterates of the stipulated map.
-/

public section

open Set
open scoped Function

namespace Chemistry.Separations

/-- The rectifying stage map `T` is the operating line followed by the inverse of the equilibrium
curve. Both curves and the displayed inverse take values in the unit interval there, and `T` is
strictly increasing there (so the monotonicity hypothesis on `[xp, x₀]` follows). If `xp` is fixed
and the operating line lies strictly below the equilibrium curve on `(xp, x₀]`, then each step
there satisfies `xp < T x < x`. All finite iterates from `x₀` remain in `(xp, x₀]` and are strictly
decreasing. -/
theorem stageStepping_cannotCrossPinch {α R xD xp x₀ : ℝ} (hα : 1 < α) (hR : 0 < R)
    (hxD : xD ∈ Ioo 0 1) (hxp : 0 ≤ xp) (hstart : xp < x₀) (hx₀ : x₀ ≤ 1) :
    let unit := Icc (0 : ℝ) 1
    let equilibrium := fun x : ℝ ↦ α * x / (1 + (α - 1) * x)
    let operating := fun x : ℝ ↦ (R * x + xD) / (R + 1)
    let inverse := fun y : ℝ ↦ y / (α - (α - 1) * y)
    let T := inverse ∘ operating
    MapsTo equilibrium unit unit ∧ MapsTo operating unit unit ∧ MapsTo inverse unit unit ∧
      InvOn inverse equilibrium unit unit ∧ StrictMonoOn T unit ∧
      (T xp = xp → (∀ x ∈ Ioc xp x₀, operating x < equilibrium x) →
        (∀ x ∈ Ioc xp x₀, xp < T x ∧ T x < x) ∧
          (∀ n : ℕ, (T^[n]) x₀ ∈ Ioc xp x₀) ∧ StrictAnti (fun n : ℕ ↦ (T^[n]) x₀)) := by
  intro unit equilibrium operating inverse T
  have hgap : 0 ≤ α - 1 := sub_nonneg.mpr hα.le
  have hαpos : 0 < α := zero_lt_one.trans hα
  have hOperatingDen : 0 < R + 1 := add_pos hR zero_lt_one
  have hEquilibriumDen {x : ℝ} (hx : x ∈ unit) : 0 < 1 + (α - 1) * x :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hgap hx.1)
  have hInverseDen {y : ℝ} (hy : y ∈ unit) : 0 < α - (α - 1) * y := by
    have h := mul_nonneg hgap (sub_nonneg.mpr hy.2)
    linarith
  have hEquilibrium : MapsTo equilibrium unit unit := by
    intro x hx
    refine ⟨div_nonneg (mul_nonneg hαpos.le hx.1) (hEquilibriumDen hx).le, ?_⟩
    apply (div_le_iff₀ (hEquilibriumDen hx)).2
    linarith [hx.2]
  have hOperating : MapsTo operating unit unit := by
    intro x hx
    refine ⟨div_nonneg (add_nonneg (mul_nonneg hR.le hx.1) hxD.1.le) hOperatingDen.le, ?_⟩
    apply (div_le_iff₀ hOperatingDen).2
    linarith [mul_le_mul_of_nonneg_left hx.2 hR.le, hxD.2]
  have hInverse : MapsTo inverse unit unit := by
    intro y hy
    refine ⟨div_nonneg hy.1 (hInverseDen hy).le, ?_⟩
    apply (div_le_iff₀ (hInverseDen hy)).2
    linarith [mul_nonneg hαpos.le (sub_nonneg.mpr hy.2)]
  have hInvOn : InvOn inverse equilibrium unit unit := by
    constructor
    · intro x hx
      apply (div_eq_iff (hInverseDen (hEquilibrium hx)).ne').2
      dsimp only [equilibrium]
      rw [mul_sub, ← mul_assoc x (α - 1), ← mul_div_assoc (x * (α - 1)),
        eq_sub_iff_add_eq, ← add_div]
      exact (div_eq_iff (hEquilibriumDen hx).ne').2 (by ring)
    · intro y hy
      apply (div_eq_iff (hEquilibriumDen (hInverse hy)).ne').2
      dsimp only [inverse]
      rw [mul_add, ← mul_assoc y (α - 1), ← mul_div_assoc α, ← mul_div_assoc (y * (α - 1)),
        ← sub_eq_iff_eq_add, ← sub_div]
      exact (div_eq_iff (hInverseDen hy).ne').2 (by ring)
  have hInverseMono : StrictMonoOn inverse unit := by
    intro a ha b hb hab
    apply (div_lt_div_iff₀ (hInverseDen ha) (hInverseDen hb)).2
    linarith [mul_lt_mul_of_pos_right hab hαpos]
  have hOperatingMono : StrictMono operating := by
    intro a b hab
    exact div_lt_div_of_pos_right
      (add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hab hR) le_rfl) hOperatingDen
  have hTMono : StrictMonoOn T unit :=
    hInverseMono.comp (hOperatingMono.strictMonoOn unit) hOperating
  refine ⟨hEquilibrium, hOperating, hInverse, hInvOn, hTMono, ?_⟩
  intro hfixed hbelow
  have hp : xp ∈ unit := ⟨hxp, hstart.le.trans hx₀⟩
  have hstep : ∀ x ∈ Ioc xp x₀, xp < T x ∧ T x < x := by
    intro x hx
    have hxUnit : x ∈ unit := ⟨hxp.trans hx.1.le, hx.2.trans hx₀⟩
    refine ⟨hfixed ▸ hTMono hp hxUnit hx.1, ?_⟩
    have h : T x < inverse (equilibrium x) :=
      hInverseMono (hOperating hxUnit) (hEquilibrium hxUnit) (hbelow x hx)
    rwa [hInvOn.1 hxUnit] at h
  have hpreserve : MapsTo T (Ioc xp x₀) (Ioc xp x₀) := fun x hx ↦
    ⟨(hstep x hx).1, (hstep x hx).2.le.trans hx.2⟩
  have horbit (n : ℕ) : (T^[n]) x₀ ∈ Ioc xp x₀ := hpreserve.iterate n ⟨hstart, le_rfl⟩
  refine ⟨hstep, horbit, strictAnti_nat_of_succ_lt ?_⟩
  intro n
  rw [Function.iterate_succ_apply']
  exact (hstep _ (horbit n)).2

end Chemistry.Separations
