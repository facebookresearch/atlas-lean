/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.DonskerVaradhan
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Tests for the Donsker–Varadhan inequality and the Gibbs variational principle
-/

@[expose] public section

open MeasureTheory Real InformationTheory
open scoped ENNReal
open MathlibExt.InformationTheory.DonskerVaradhan

namespace MathlibExtTest.InformationTheory.DonskerVaradhan

/-- The Donsker–Varadhan inequality with `f = cos` between two Dirac masses on `ℝ`. -/
example : ENNReal.ofReal (∫ x, cos x ∂(Measure.dirac (0 : ℝ)) -
      log (∫ x, exp (cos x) ∂(Measure.dirac (1 : ℝ)))) ≤
    klDiv (Measure.dirac (0 : ℝ)) (Measure.dirac (1 : ℝ)) :=
  ofReal_integral_sub_log_integral_exp_le_klDiv (by fun_prop) (C := 1) abs_cos_le_one

/-- Against itself, the bound reads `∫ f dμ ≤ log ∫ exp f dμ` (Jensen). -/
example : ∫ x, cos x ∂(Measure.dirac (0 : ℝ)) - log (∫ x, exp (cos x) ∂(Measure.dirac (0 : ℝ)))
    ≤ (klDiv (Measure.dirac (0 : ℝ)) (Measure.dirac (0 : ℝ))).toReal :=
  integral_sub_log_integral_exp_le_toReal_klDiv (by simp [klDiv_self]) (by fun_prop)
    (C := 1) abs_cos_le_one

/-- The Gibbs variational principle for `f = sin` under a Dirac mass. -/
example : IsGreatest {r : ℝ | ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      klDiv μ (Measure.dirac (0 : ℝ)) ≠ ⊤ ∧
      r = ∫ x, sin x ∂μ - (klDiv μ (Measure.dirac (0 : ℝ))).toReal}
    (log (∫ x, exp (sin x) ∂(Measure.dirac (0 : ℝ)))) :=
  isGreatest_integral_sub_klDiv (by fun_prop) (C := 1) abs_sin_le_one

end MathlibExtTest.InformationTheory.DonskerVaradhan
