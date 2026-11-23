/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ElementaryItoIntegral
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Tests for the elementary Itô integral

A non-vacuity witness for `ElementaryIntegrand`, the single-interval integrand at times before,
inside and after its interval, the endpoint conventions of `(a, b]`, the degenerate interval
`a = b`, the empty integrand, a concrete Itô isometry `E[(B 2 - B 1)²] = 1`, and the martingale
property of a concrete elementary integral.
-/

open MeasureTheory ProbabilityTheory ProbabilityTheory.ElementaryIntegrand
open scoped NNReal

namespace MathlibExtTest.Probability.ElementaryItoIntegral

/-- `norm_num` for inequalities between `ℝ≥0` numerals, through the coercion to `ℝ`. -/
local macro "nnle" : term => `(by rw [← NNReal.coe_le_coe]; norm_num)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

/-- The integrand `1_{(1, 2]}`, a non-vacuity witness for `ElementaryIntegrand`. -/
noncomputable def one12 (F : Filtration ℝ≥0 mΩ) : ElementaryIntegrand F :=
  single 1 2 (by norm_num) (fun _ ↦ (1 : ℝ)) measurable_const 1 (by simp)

example : (one12 F).n = 1 := rfl

/-- Inside the interval the integrand is `1`; the left endpoint is excluded, the right one
included. -/
example (ω : Ω) : (one12 F).toProcess (3 / 2) ω = 1 := by
  rw [one12, toProcess_single]
  exact Set.indicator_of_mem (by
    simp only [Set.mem_Ioc, ← NNReal.coe_lt_coe, ← NNReal.coe_le_coe]; norm_num) _

example (ω : Ω) : (one12 F).toProcess 1 ω = 0 := by
  rw [one12, toProcess_single]
  exact Set.indicator_of_notMem (by simp) _

example (ω : Ω) : (one12 F).toProcess 2 ω = 1 := by
  rw [one12, toProcess_single]
  exact Set.indicator_of_mem (by
    simp only [Set.mem_Ioc, ← NNReal.coe_lt_coe, ← NNReal.coe_le_coe]; norm_num) _

/-- After the interval the integral is the full increment `B 2 - B 1`. -/
example (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (one12 F).itoIntegral B 3 ω = B 2 ω - B 1 ω := by
  rw [one12, itoIntegral_single, min_eq_left nnle, min_eq_left nnle, one_mul]

/-- Inside the interval only the increment up to time `t` counts. -/
example (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (one12 F).itoIntegral B (3 / 2) ω = B (3 / 2) ω - B 1 ω := by
  rw [one12, itoIntegral_single, min_eq_right nnle, min_eq_left nnle, one_mul]

/-- Before the interval the integral vanishes. -/
example (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : (one12 F).itoIntegral B (1 / 2) ω = 0 := by
  rw [one12, itoIntegral_single, min_eq_right nnle, min_eq_right nnle]
  ring

/-- A degenerate interval `(a, a]` integrates to `0`. -/
example (B : ℝ≥0 → Ω → ℝ) (ξ : Ω → ℝ) (hξ : Measurable[F 1] ξ) (C : ℝ)
    (hξC : ∀ ω, |ξ ω| ≤ C) (t : ℝ≥0) (ω : Ω) :
    (single 1 1 le_rfl ξ hξ C hξC).itoIntegral B t ω = 0 := by
  rw [itoIntegral_single, sub_self, mul_zero]

/-- The empty integrand (no intervals; its bound may even be negative). -/
def empty (F : Filtration ℝ≥0 mΩ) : ElementaryIntegrand F where
  n := 0
  time := fun _ ↦ 0
  monotone_time := fun _ _ _ ↦ le_rfl
  coeff := fun i ↦ i.elim0
  measurable_coeff := fun i ↦ i.elim0
  bound := -1
  abs_coeff_le := fun i ↦ i.elim0

example (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : (empty F).itoIntegral B t ω = 0 := by
  simp [itoIntegral, empty]

example (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : (one12 F).itoIntegral B 0 ω = 0 := by
  simp

/-- The time integral of `(1_{(1, 2]})²` over `[0, 3]` is `1`. -/
example (ω : Ω) :
    ∫ u in (0 : ℝ)..(3 : ℝ≥0), (one12 F).toProcess (Real.toNNReal u) ω ^ 2 = 1 := by
  rw [integral_toProcess_sq]
  change ∑ _ : Fin 1, _ = _
  simp [one12, single]
  norm_num

/-- **Concrete Itô isometry**: `E[(B 2 - B 1)²] = 1` for a Brownian motion with independent
increments relative to `F`. -/
example {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) :
    P[fun ω ↦ (one12 F).itoIntegral B 3 ω ^ 2] = 1 := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  rw [integral_itoIntegral_sq_eq_sum _ hB hBF hInd]
  change ∑ _ : Fin 1, _ = _
  simp [one12, single]
  norm_num

/-- The concrete integral `t ↦ B (2 ∧ t) - B (1 ∧ t)` is a martingale. -/
example {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P) :
    Martingale ((one12 F).itoIntegral B) F P :=
  martingale_itoIntegral _ hB hBF hInd

end MathlibExtTest.Probability.ElementaryItoIntegral
