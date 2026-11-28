/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.PACLearning.UniformConvergence
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Regressions for representative samples and uniform convergence -/

namespace CSLibExtTest.MachineLearning.PACLearning

open MeasureTheory ProbabilityTheory Cslib.MachineLearning.PACLearning
open CSLibExt.MachineLearning.GeneralizationBounds (empiricalRisk risk)

private def loss (h : Bool) (z : ℝ) : ℝ := if h then z else 0

-- The boundary is included; the hypothesis with nonzero deviation witnesses failure
-- below the boundary, even though the other hypothesis has zero deviation.
example : IsRepresentative loss (Measure.dirac (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) 1 ∧
    ¬ IsRepresentative loss (Measure.dirac (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) (1 / 2) := by
  constructor
  · intro h
    refine ⟨integrable_dirac (by simp), ?_⟩
    cases h <;> norm_num [loss, empiricalRisk, risk, integral_dirac, Fin.sum_univ_one]
  · intro h
    have h' := (h true).2
    norm_num [loss, empiricalRisk, risk, integral_dirac, Fin.sum_univ_one] at h'

private noncomputable def half : unitInterval := ⟨1 / 2, by norm_num [Set.mem_Icc]⟩

private noncomputable def heavyLoss (_ : Unit) (n : ℕ) : ℝ :=
  if n = 0 then 0 else 2 ^ n

private theorem not_integrable_heavyLoss : ¬ Integrable (heavyLoss ()) (geometricMeasure half) := by
  intro h
  have hp : half ≠ 0 := by
    intro heq
    have hv := congrArg Subtype.val heq
    norm_num [half] at hv
  have hs := (integrable_geometricMeasure_iff hp).mp h
  have ht := hs.comp_injective Nat.succ_injective
  have hc : Summable (fun _ : ℕ => (1 / 2 : ℝ)) := ht.congr fun n => by
    change (1 - (1 / 2 : ℝ)) ^ (n + 1) * (1 / 2) * ‖heavyLoss () (n + 1)‖ = 1 / 2
    simp only [heavyLoss, Nat.succ_ne_zero, ite_false, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
    calc
      _ = ((1 - (1 / 2 : ℝ)) * 2) ^ (n + 1) * (1 / 2) := by rw [mul_pow]; ring
      _ = 1 / 2 := by norm_num
  have hzero := tendsto_nhds_unique hc.tendsto_atTop_zero tendsto_const_nhds
  norm_num at hzero

-- The old real-risk inequality holds at the zero sample, but the geometric tail
-- contributes `1/2` at every positive index and makes the loss nonintegrable.
example :
    |empiricalRisk heavyLoss (fun _ : Fin 1 => 0) () - risk heavyLoss (geometricMeasure half) ()|
        ≤ (1 / 2 : ℝ) ∧
      ¬ IsRepresentative heavyLoss (geometricMeasure half) (fun _ : Fin 1 => 0) (1 / 2) := by
  refine ⟨?_, fun h => not_integrable_heavyLoss (h ()).1⟩
  have hr : risk heavyLoss (geometricMeasure half) () = 0 := integral_undef not_integrable_heavyLoss
  rw [hr]
  norm_num [heavyLoss, empiricalRisk, Fin.sum_univ_one]

-- The nonconstant loss also gives a measurable event for the two-hypothesis class.
example (D : Measure ℝ) [IsProbabilityMeasure D] :
    MeasurableSet {S : Fin 1 → ℝ | IsRepresentative loss D S (1 / 2)} := by
  apply measurableSet_isRepresentative
  intro h
  cases h
  · exact measurable_const
  · exact measurable_id

-- Zero loss gives one common threshold for all distributions and positive sample sizes.
example {Z : Type*} [MeasurableSpace Z] :
    HasUniformConvergence (fun (_ : Unit) (_ : Z) => (0 : ℝ)) := by
  refine ⟨fun _ _ => 1, ?_⟩
  intro ε δ hε hδ D _ m _ _
  have hevent : {S : Fin m → Z | IsRepresentative (fun (_ : Unit) _ => 0) D S ε} =
      Set.univ := by
    ext S
    simp [IsRepresentative, empiricalRisk, risk, hε.1.le]
  rw [hevent, probReal_univ]
  exact ⟨MeasurableSet.univ, by linarith [hδ.1]⟩

end CSLibExtTest.MachineLearning.PACLearning
