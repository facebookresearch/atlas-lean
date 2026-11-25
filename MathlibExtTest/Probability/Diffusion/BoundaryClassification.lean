/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Diffusion.BoundaryClassification
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Topology.ContinuousOn

/-!
# Tests for the Feller boundary predicates

Every predicate carries the standing hypotheses: an interior basepoint and a positive diffusion
coefficient are necessary. For the degenerate coefficient `a = 0` both Feller integrability
conditions hold, since the speed density vanishes by division by zero, yet the endpoint is not
classified as regular; an endpoint basepoint is rejected as well. Brownian motion on `(0, 1)`
(`b = 0`, `a = 1`) has both endpoints regular, so the predicates are not vacuous. Basepoint
independence is applied to constant coefficients.
-/

open MeasureTheory Set
open MathlibExt.Probability.Diffusion

@[expose] public section
namespace MathlibExtTest.Probability.Diffusion.BoundaryClassification

/-! ### Each class requires an interior basepoint and a positive diffusion coefficient -/

example (b a : ℝ → ℝ) (c : ℝ) (h : IsRegularBoundaryAtZero b a c) :
    c ∈ Ioo (0 : ℝ) 1 ∧ ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x := ⟨h.1.mem_Ioo, h.1.pos⟩

example (b a : ℝ → ℝ) (c : ℝ) (h : IsExitBoundaryAtZero b a c) :
    c ∈ Ioo (0 : ℝ) 1 ∧ ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x := ⟨h.1.mem_Ioo, h.1.pos⟩

example (b a : ℝ → ℝ) (c : ℝ) (h : IsEntranceBoundaryAtZero b a c) :
    c ∈ Ioo (0 : ℝ) 1 ∧ ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x := ⟨h.1.mem_Ioo, h.1.pos⟩

example (b a : ℝ → ℝ) (c : ℝ) (h : IsNaturalBoundaryAtZero b a c) :
    c ∈ Ioo (0 : ℝ) 1 ∧ ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x := ⟨h.1.mem_Ioo, h.1.pos⟩

example (b a : ℝ → ℝ) (c : ℝ) (h : IsRegularBoundaryAtOne b a c) :
    c ∈ Ioo (0 : ℝ) 1 ∧ ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x := ⟨h.1.mem_Ioo, h.1.pos⟩

example (b a : ℝ → ℝ) (c : ℝ) (h : IsExitBoundaryAtOne b a c) :
    c ∈ Ioo (0 : ℝ) 1 ∧ ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x := ⟨h.1.mem_Ioo, h.1.pos⟩

example (b a : ℝ → ℝ) (c : ℝ) (h : IsEntranceBoundaryAtOne b a c) :
    c ∈ Ioo (0 : ℝ) 1 ∧ ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x := ⟨h.1.mem_Ioo, h.1.pos⟩

example (b a : ℝ → ℝ) (c : ℝ) (h : IsNaturalBoundaryAtOne b a c) :
    c ∈ Ioo (0 : ℝ) 1 ∧ ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x := ⟨h.1.mem_Ioo, h.1.pos⟩

/-! ### Invalid basepoints -/

-- The basepoint `0` makes `Ioo 0 c` empty; it is rejected even for a degenerate coefficient.
example : ¬ IsRegularBoundaryAtZero (fun _ => 0) (fun _ => 0) 0 :=
  fun h => lt_irrefl 0 h.1.mem_Ioo.1

example : ¬ IsRegularBoundaryAtZero (fun _ => 0) (fun _ => 1) 0 :=
  fun h => lt_irrefl 0 h.1.mem_Ioo.1

-- The basepoint `1` makes `Ioo c 1` empty.
example : ¬ IsRegularBoundaryAtOne (fun _ => 0) (fun _ => 1) 1 :=
  fun h => lt_irrefl 1 h.1.mem_Ioo.2

/-! ### A degenerate diffusion coefficient -/

/-- With `a = 0` the speed density is `0` by division by zero, so both Feller integrability
conditions at `0` hold, but the endpoint is not regular. -/
example :
    IntegrableOn (fun x => (∫ y in x..(1 / 2 : ℝ),
        speedDensityFrom (fun _ => 0) (fun _ => 0) (1 / 2) y) *
      scaleDensityFrom (fun _ => 0) (fun _ => 0) (1 / 2) x) (Ioo 0 (1 / 2)) volume ∧
    IntegrableOn (fun x => (∫ y in x..(1 / 2 : ℝ),
        scaleDensityFrom (fun _ => 0) (fun _ => 0) (1 / 2) y) *
      speedDensityFrom (fun _ => 0) (fun _ => 0) (1 / 2) x) (Ioo 0 (1 / 2)) volume ∧
    ¬ IsRegularBoundaryAtZero (fun _ => 0) (fun _ => 0) (1 / 2) := by
  have hm : ∀ y, speedDensityFrom (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (1 / 2) y = 0 := by
    intro y
    simp [speedDensityFrom]
  refine ⟨?_, ?_, fun h => lt_irrefl 0 (h.1.pos (1 / 2) (by norm_num))⟩
  · simp only [hm, intervalIntegral.integral_zero, zero_mul]
    exact integrableOn_zero
  · simp only [hm, mul_zero]
    exact integrableOn_zero

example : ¬ IsRegularBoundaryAtOne (fun _ => 0) (fun _ => 0) (1 / 2) :=
  fun h => lt_irrefl 0 (h.1.pos (1 / 2) (by norm_num))

/-! ### Brownian motion on `(0, 1)`: both endpoints are regular -/

theorem brownian_scaleDensityFrom (y : ℝ) :
    scaleDensityFrom (fun _ => 0) (fun _ => 1) (1 / 2) y = 1 := by
  simp [scaleDensityFrom]

theorem brownian_speedDensityFrom (y : ℝ) :
    speedDensityFrom (fun _ => 0) (fun _ => 1) (1 / 2) y = 2 := by
  simp only [speedDensityFrom, brownian_scaleDensityFrom, mul_one, div_one]

theorem brownian_isFellerAdmissible :
    IsFellerAdmissible (fun _ => 0) (fun _ => 1) (1 / 2) where
  mem_Ioo := by norm_num
  pos := fun _ _ => one_pos
  continuousOn := continuousOn_const
  continuousOn_div := by fun_prop

example : IsRegularBoundaryAtZero (fun _ => 0) (fun _ => 1) (1 / 2) := by
  refine ⟨brownian_isFellerAdmissible, ?_, ?_⟩
  · simp only [brownian_speedDensityFrom, brownian_scaleDensityFrom,
      intervalIntegral.integral_const, smul_eq_mul, mul_one]
    exact ((by fun_prop : Continuous fun x : ℝ => (1 / 2 - x) * 2).integrableOn_Icc
      (a := 0) (b := 1 / 2)).mono_set Ioo_subset_Icc_self
  · simp only [brownian_speedDensityFrom, brownian_scaleDensityFrom,
      intervalIntegral.integral_const, smul_eq_mul, mul_one]
    exact ((by fun_prop : Continuous fun x : ℝ => (1 / 2 - x) * 2).integrableOn_Icc
      (a := 0) (b := 1 / 2)).mono_set Ioo_subset_Icc_self

example : IsRegularBoundaryAtOne (fun _ => 0) (fun _ => 1) (1 / 2) := by
  refine ⟨brownian_isFellerAdmissible, ?_, ?_⟩
  · simp only [brownian_speedDensityFrom, brownian_scaleDensityFrom,
      intervalIntegral.integral_const, smul_eq_mul, mul_one]
    exact ((by fun_prop : Continuous fun x : ℝ => (x - 1 / 2) * 2).integrableOn_Icc
      (a := 1 / 2) (b := 1)).mono_set Ioo_subset_Icc_self
  · simp only [brownian_speedDensityFrom, brownian_scaleDensityFrom,
      intervalIntegral.integral_const, smul_eq_mul, mul_one]
    exact ((by fun_prop : Continuous fun x : ℝ => (x - 1 / 2) * 2).integrableOn_Icc
      (a := 1 / 2) (b := 1)).mono_set Ioo_subset_Icc_self

/-! ### Basepoint independence -/

example : IsRegularBoundaryAtZero (fun _ : ℝ => 0) (fun _ : ℝ => 1) (1 / 3 : ℝ) ↔
    IsRegularBoundaryAtZero (fun _ : ℝ => 0) (fun _ : ℝ => 1) (1 / 2 : ℝ) := by
  apply isRegularBoundaryAtZero_basepoint_iff
  · intro x _
    exact zero_lt_one
  · exact continuousOn_const
  · exact continuousOn_const
  · norm_num [Set.mem_Ioo]
  · norm_num [Set.mem_Ioo]

example : IsNaturalBoundaryAtOne (fun _ : ℝ => 0) (fun _ : ℝ => 1) (1 / 3 : ℝ) ↔
    IsNaturalBoundaryAtOne (fun _ : ℝ => 0) (fun _ : ℝ => 1) (1 / 2 : ℝ) := by
  apply isNaturalBoundaryAtOne_basepoint_iff
  · intro x _
    exact zero_lt_one
  · exact continuousOn_const
  · exact continuousOn_const
  · norm_num [Set.mem_Ioo]
  · norm_num [Set.mem_Ioo]

#print axioms isRegularBoundaryAtZero_basepoint_iff
#print axioms isExitBoundaryAtZero_basepoint_iff
#print axioms isEntranceBoundaryAtZero_basepoint_iff
#print axioms isNaturalBoundaryAtZero_basepoint_iff
#print axioms isRegularBoundaryAtOne_basepoint_iff
#print axioms isExitBoundaryAtOne_basepoint_iff
#print axioms isEntranceBoundaryAtOne_basepoint_iff
#print axioms isNaturalBoundaryAtOne_basepoint_iff

end MathlibExtTest.Probability.Diffusion.BoundaryClassification
