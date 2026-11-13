/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.PetersonIdentification
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime

namespace MathlibExtTest.Probability.Statistics.PetersonIdentification

/-! ### Point-mass laws, computed from the definitions -/

/-- The observed-data law of point masses is the point mass at the observation. -/
theorem censoredObsLaw_dirac (a b : ℝ) :
    censoredObsLaw (Measure.dirac a) (Measure.dirac b) =
      Measure.dirac (censoredObsMap (a, b)) := by
  rw [censoredObsLaw, Measure.dirac_prod_dirac, Measure.map_dirac' measurable_censoredObsMap]

/-- The at-risk mass of a point-mass observed-data law, computed from `obsAtRisk`. -/
theorem obsAtRisk_dirac (x : ℝ) (b : Bool) (s : ℝ) :
    obsAtRisk (Measure.dirac (x, b)) s = if s ≤ x then 1 else 0 := by
  rw [obsAtRisk, Measure.dirac_apply' _ (measurableSet_Ici.prod MeasurableSet.univ)]
  by_cases h : s ≤ x <;> simp [h, indicator]

/-! ### Non-vacuity: different censoring laws, same observed-data law -/

/-- **Two different censoring laws give the same observed-data law** (computed, not via the
theorems): with failure at `0`, censoring at `1` and censoring at `2` both give the point mass at
`(0, failure)`, and the observed at-risk mass at `0` is `1`. So the hypotheses of the
unknown-censoring theorems hold with `G ≠ G'`. -/
example : Measure.dirac (1 : ℝ) ≠ Measure.dirac 2 ∧
    censoredObsLaw (Measure.dirac (0 : ℝ)) (Measure.dirac 1) =
      censoredObsLaw (Measure.dirac (0 : ℝ)) (Measure.dirac 2) ∧
    obsAtRisk (censoredObsLaw (Measure.dirac (0 : ℝ)) (Measure.dirac 1)) 0 = 1 := by
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have := congrArg (fun μ : Measure ℝ => μ {1}) h
    simp [Measure.dirac_apply' _ (measurableSet_singleton _)] at this
  · rw [censoredObsLaw_dirac, censoredObsLaw_dirac]
    congr 1
    simp only [censoredObsMap, obsTime, Prod.mk.injEq]
    norm_num
  · rw [censoredObsLaw_dirac, obsAtRisk_dirac]
    simp [censoredObsMap, obsTime]

/-- Usage of `restrict_Iic_eq_of_censoredObsLaw_eq_of_atRisk` with two different censoring laws
(`δ₁` and `δ₂`) and the at-risk condition at `h = 0`. -/
example : (Measure.dirac (0 : ℝ)).restrict (Iic 0) = (Measure.dirac (0 : ℝ)).restrict (Iic 0) :=
  restrict_Iic_eq_of_censoredObsLaw_eq_of_atRisk (G := Measure.dirac 1) (G' := Measure.dirac 2)
    (by
      rw [censoredObsLaw_dirac, censoredObsLaw_dirac]
      congr 1
      simp only [censoredObsMap, obsTime, Prod.mk.injEq]
      norm_num)
    (by rw [censoredObsLaw_dirac, obsAtRisk_dirac]; simp [censoredObsMap, obsTime])

/-- Usage of the Peterson representation: the hazard of `δ₀` on `(-∞, 0]` is the observed-failure
sub-distribution divided by the at-risk mass, for censoring at `1`. -/
example : (hazardMeasure (Measure.dirac (0 : ℝ))).restrict (Iic 0) =
    ((obsFailMeasure (censoredObsLaw (Measure.dirac (0 : ℝ)) (Measure.dirac 1))).restrict
      (Iic 0)).withDensity fun s =>
        (obsAtRisk (censoredObsLaw (Measure.dirac (0 : ℝ)) (Measure.dirac 1)) s)⁻¹ :=
  hazardMeasure_restrict_Iic_eq_peterson
    (by rw [censoredObsLaw_dirac, obsAtRisk_dirac]; simp [censoredObsMap, obsTime])

/-! ### Boundary: the at-risk condition cannot be dropped -/

/-- **Nothing is identified outside the at-risk set** (computed, not via the theorems): with
censoring at `-1` every subject is censored before failing, so failure laws `δ₀` and `δ₅` give the
same observed-data law `δ_{(-1, censored)}`. At `h = 0` the at-risk mass `P(X ≥ 0)` is `0`, and
the two laws differ on `(-∞, 0]`. -/
example : censoredObsLaw (Measure.dirac (0 : ℝ)) (Measure.dirac (-1)) =
      censoredObsLaw (Measure.dirac (5 : ℝ)) (Measure.dirac (-1)) ∧
    obsAtRisk (censoredObsLaw (Measure.dirac (0 : ℝ)) (Measure.dirac (-1))) 0 = 0 ∧
    (Measure.dirac (0 : ℝ)).restrict (Iic 0) ≠ (Measure.dirac (5 : ℝ)).restrict (Iic 0) := by
  refine ⟨?_, ?_, fun h => ?_⟩
  · rw [censoredObsLaw_dirac, censoredObsLaw_dirac]
    congr 1
    simp only [censoredObsMap, obsTime, Prod.mk.injEq]
    norm_num
  · rw [censoredObsLaw_dirac, obsAtRisk_dirac]
    simp only [censoredObsMap, obsTime]
    norm_num
  · have := congrArg (fun μ : Measure ℝ => μ univ) h
    simp only [Measure.restrict_apply_univ, Measure.dirac_apply' _ measurableSet_Iic] at this
    norm_num [indicator] at this

/-- Boundary: the at-risk set of censoring at `1` with failure at `0` is `(-∞, 0]`; it contains
its right end `0` but no later time. -/
example : atRiskSet (censoredObsLaw (Measure.dirac (0 : ℝ)) (Measure.dirac 1)) = Iic 0 := by
  ext s
  simp only [atRiskSet, mem_ofPred_eq, mem_Iic, censoredObsLaw_dirac, obsAtRisk_dirac,
    censoredObsMap, obsTime]
  norm_num

end MathlibExtTest.Probability.Statistics.PetersonIdentification
