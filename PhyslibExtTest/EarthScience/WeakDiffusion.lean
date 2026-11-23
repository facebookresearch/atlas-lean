/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PhyslibExt.EarthScience.WeakDiffusion

/-!
# Weak diffusion checks

Concrete consumers of `PhyslibExt.EarthScience.WeakDiffusion`: constant
diffusivity with a constant source, tested against `x * (1 - x)`, and the
zero-source case, whose solution vanishes.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`κ = 1` and `f = 2`, the theorem's hypotheses hold and its weak solution
`u`, tested against `v(x) = x * (1 - x)`, gives
`∫₀¹ u' v' = ∫₀¹ 2 * x * (1 - x) = 1 / 3`. With `κ(x) = 1 + x` and `f = 0`,
the zero function solves the weak problem, so by uniqueness the solution
vanishes on `[0,1]`, in particular at both endpoints.

## ii. Key results

No new results are introduced here; the private definitions `quadWeak`
and `zeroWeak` are the test functions `x * (1 - x)` and `0` as `WeakH10`
values.

## iii. Table of contents

- A. Concrete test function `x * (1 - x)` in `H¹₀(0,1)`
- B. Constant diffusivity, source `2`
- C. Zero source with `κ(x) = 1 + x`: vanishing solution

## iv. References

- `PhyslibExt.EarthScience.WeakDiffusion`
-/

open MeasureTheory

/-! ## A. Concrete test function `x * (1 - x)` in `H¹₀(0,1)` -/

/-- The quadratic `x * (1 - x)` as an `H¹₀(0,1)` function, with weak
derivative `1 - 2 * x`. -/
private def quadWeak : EarthScience.WeakH10 where
  toFun := fun x => x * (1 - x)
  weakDeriv := fun x => 1 - 2 * x
  weakDeriv_memLp := by
    have hB : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ‖(1 : ℝ) - 2 * x‖ ≤ 3 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs]
      have hx' := Set.mem_Icc.mp hx
      rw [abs_le]
      constructor <;> linarith
    exact MemLp.of_bound
      (by fun_prop : Continuous fun x : ℝ => 1 - 2 * x).aestronglyMeasurable 3 hB
  toFun_eq_integral := by
    intro x hx
    have hx' : 0 ≤ x := (Set.mem_Icc.mp hx).1
    have hInt : IntervalIntegrable (fun t : ℝ => 1 - 2 * t) volume 0 x :=
      (by fun_prop : Continuous fun t : ℝ => 1 - 2 * t).intervalIntegrable 0 x
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := x)
      (f := fun t => t - t ^ 2) (f' := fun t => 1 - 2 * t)
      (fun t _ => by
        convert (hasDerivAt_id' t).sub (hasDerivAt_pow 2 t) using 1
        ring) hInt
    rw [show (∫ t in (0 : ℝ)..x, (1 - 2 * t)) = (x - x ^ 2) - (0 - (0 : ℝ) ^ 2) from hFTC]
    ring
  integral_weakDeriv_eq_zero := by
    have hInt : IntervalIntegrable (fun t : ℝ => 1 - 2 * t) volume 0 1 :=
      (by fun_prop : Continuous fun t : ℝ => 1 - 2 * t).intervalIntegrable 0 1
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := fun t => t - t ^ 2) (f' := fun t => 1 - 2 * t)
      (fun t _ => by
        convert (hasDerivAt_id' t).sub (hasDerivAt_pow 2 t) using 1
        ring) hInt
    rw [show (∫ t in (0 : ℝ)..1, (1 - 2 * t)) = (1 - (1 : ℝ) ^ 2) - (0 - (0 : ℝ) ^ 2) from hFTC]
    norm_num

/-! ## B. Constant diffusivity, source `2` -/

/-- With `κ = 1` and `f = 2`, the theorem gives a weak solution `u`, and
testing its weak equation against `quadWeak` (that is, `x * (1 - x)`) gives
`∫₀¹ u' * (1 - 2 * x) = ∫₀¹ 2 * (x * (1 - x)) = 1 / 3`. -/
example : ∃ u : EarthScience.WeakH10,
    (∀ v : EarthScience.WeakH10,
      ∫ x in (0 : ℝ)..1, (1 : ℝ) * u.weakDeriv x * v.weakDeriv x
        = ∫ x in (0 : ℝ)..1, (2 : ℝ) * v.toFun x)
    ∧ ∫ x in (0 : ℝ)..1, (1 : ℝ) * u.weakDeriv x * quadWeak.weakDeriv x = 1 / 3 := by
  obtain ⟨u, hu, -⟩ := EarthScience.weak_diffusion_exists_unique
    (κ := fun _ => (1 : ℝ)) (f := fun _ => (2 : ℝ)) (kmin := 1) (kmax := 1)
    (by norm_num) aestronglyMeasurable_const
    (Filter.Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩) (memLp_const 2)
  refine ⟨u, hu, (hu quadWeak).trans ?_⟩
  show ∫ x in (0 : ℝ)..1, (2 : ℝ) * (x * (1 - x)) = 1 / 3
  have hInt : IntervalIntegrable (fun t : ℝ => 2 * t - 2 * t ^ 2) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => 2 * t - 2 * t ^ 2).intervalIntegrable 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := (1 : ℝ))
    (f := fun t => t ^ 2 - (2 / 3) * t ^ 3) (f' := fun t => 2 * t - 2 * t ^ 2)
    (fun t _ => by
      convert (hasDerivAt_pow 2 t).sub
        ((hasDerivAt_pow 3 t).const_mul (2 / 3 : ℝ)) using 1
      ring) hInt
  have hEq : (fun x : ℝ => (2 : ℝ) * (x * (1 - x))) = fun x => 2 * x - 2 * x ^ 2 := by
    funext x
    ring
  rw [hEq, show (∫ x in (0 : ℝ)..1, (2 * x - 2 * x ^ 2))
      = ((1 : ℝ) ^ 2 - (2 / 3) * (1 : ℝ) ^ 3) - ((0 : ℝ) ^ 2 - (2 / 3) * (0 : ℝ) ^ 3)
    from hFTC]
  norm_num

/-! ## C. Zero source with `κ(x) = 1 + x`: vanishing solution -/

/-- The zero function as an `H¹₀(0,1)` function. -/
private def zeroWeak : EarthScience.WeakH10 where
  toFun := 0
  weakDeriv := 0
  weakDeriv_memLp := MemLp.zero
  toFun_eq_integral := by
    intro x _
    simp
  integral_weakDeriv_eq_zero := by simp

/-- With `κ(x) = 1 + x` and zero source, `zeroWeak` solves the weak problem,
so by uniqueness the weak solution vanishes on `[0,1]`, in particular at both
endpoints. -/
example : ∃ u : EarthScience.WeakH10,
    Set.EqOn u.toFun 0 (Set.Icc 0 1) ∧ u.toFun 0 = 0 ∧ u.toFun 1 = 0 := by
  obtain ⟨u, -, huniq⟩ := EarthScience.weak_diffusion_exists_unique
    (κ := fun x => 1 + x) (f := fun _ => (0 : ℝ)) (kmin := 1) (kmax := 2)
    (by norm_num)
    (continuous_const.add continuous_id).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hx' := Set.mem_Icc.mp hx
      constructor <;> linarith)
    (memLp_const 0)
  have hzero : ∀ v : EarthScience.WeakH10,
      ∫ x in (0 : ℝ)..1, (1 + x) * zeroWeak.weakDeriv x * v.weakDeriv x
        = ∫ x in (0 : ℝ)..1, (0 : ℝ) * v.toFun x := by
    intro v
    have h0 : zeroWeak.weakDeriv = (0 : ℝ → ℝ) := rfl
    rw [h0]
    simp
  have hEq := huniq zeroWeak hzero
  refine ⟨u, hEq.symm, ?_, ?_⟩
  · exact hEq.symm (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩)
  · exact hEq.symm (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩)
