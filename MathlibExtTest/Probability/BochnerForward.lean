/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BochnerForward
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Tests for Bochner forward compatibility

Tests cover normalization, both parts of positive definiteness, the affine counterexample,
and a nonconstant Dirac characteristic function.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

/-- The constant function `1` is a characteristic function, witnessed by the
Dirac measure at `0`. -/
example : IsCharacteristicFun (fun _ : ℝ => 1) := by
  refine ⟨Measure.dirac 0, inferInstance, fun t => ?_⟩
  simp [charFun_dirac]

/-- The constant function `1` is a real characteristic function. -/
example : IsCharacteristicFunReal (fun _ : ℝ => 1) := by
  have h : IsCharacteristicFun (fun _ : ℝ => 1) :=
    ⟨Measure.dirac 0, inferInstance, fun t => by simp [charFun_dirac]⟩
  exact h

/-- Bochner's forward direction applied to the constant characteristic
function `1`: it is continuous, positive definite, and `1` at `0`. -/
example : Continuous (fun _ : ℝ => (1 : ℂ)) ∧
    IsPositiveDefinite (fun _ : ℝ => (1 : ℂ)) ∧ (fun _ : ℝ => (1 : ℂ)) 0 = 1 := by
  have h : IsCharacteristicFun (fun _ : ℝ => (1 : ℂ)) :=
    ⟨Measure.dirac 0, inferInstance, fun t => by simp [charFun_dirac]⟩
  exact bochner_forward _ h

/-- The constant function `2` is not a characteristic function: Bochner's
forward direction would force its value at `0` to be `1`. -/
example : ¬ IsCharacteristicFun (fun _ : ℝ => (2 : ℂ)) := by
  intro h
  have h0 := (bochner_forward _ h).2.2
  norm_num at h0

/-- The constant function `2` is not a real characteristic function. -/
example : ¬ IsCharacteristicFunReal (fun _ : ℝ => 2) := by
  intro h
  have h0 := (bochner_forward_real _ h).2.2
  norm_num at h0

/-- A two-point characteristic-function quadratic form is real and nonnegative. -/
example (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    (∑ i, ∑ j, charFun μ (t i - t j) * z i * starRingEnd ℂ (z j)).im = 0 ∧
      0 ≤ (∑ i, ∑ j, charFun μ (t i - t j) * z i * starRingEnd ℂ (z j)).re :=
  charFun_isPositiveDefinite μ 2 t z

/-- The affine function `1 + t` fails reality of its two-point quadratic form. -/
example : ¬ IsPositiveDefinite (fun t : ℝ => 1 + (t : ℂ)) := by
  intro h
  have him := (h 2 ![0, 1] ![1, Complex.I]).1
  norm_num [Fin.sum_univ_two, Complex.mul_im, Complex.mul_re] at him

/-- The same affine function is excluded by the real-valued predicate. -/
example : ¬ IsPositiveDefiniteReal (fun t : ℝ => 1 + t) := by
  intro h
  have him := (h 2 ![0, 1] ![1, Complex.I]).1
  norm_num [Fin.sum_univ_two, Function.comp_apply, Complex.mul_im, Complex.mul_re] at him

/-- A nonconstant Dirac characteristic function satisfies both quadratic-form conditions. -/
example :
    (∑ i : Fin 2, ∑ j : Fin 2,
      charFun (Measure.dirac (1 : ℝ)) (![0, 1] i - ![0, 1] j) *
        ![1, Complex.I] i * starRingEnd ℂ (![1, Complex.I] j)).im = 0 ∧
    0 ≤ (∑ i : Fin 2, ∑ j : Fin 2,
      charFun (Measure.dirac (1 : ℝ)) (![0, 1] i - ![0, 1] j) *
        ![1, Complex.I] i * starRingEnd ℂ (![1, Complex.I] j)).re :=
  charFun_isPositiveDefinite (Measure.dirac (1 : ℝ)) 2 ![0, 1] ![1, Complex.I]

#print axioms ProbabilityTheory.bochner_forward
#print axioms ProbabilityTheory.bochner_forward_real
#print axioms ProbabilityTheory.charFun_isPositiveDefinite
