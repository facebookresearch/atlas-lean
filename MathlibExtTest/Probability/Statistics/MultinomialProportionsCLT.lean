/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.MultinomialProportionsCLT
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped ENNReal Real

namespace MultinomialProportionsCLTTest

private noncomputable def p : Fin 3 → ℝ := ![1 / 2, 1 / 2, 0]

private theorem p_nonneg (i : Fin 3) : 0 ≤ p i := by
  fin_cases i <;> norm_num [p]

private theorem p_sum : ∑ i, p i = 1 := by
  norm_num [p, Fin.sum_univ_succ]

private noncomputable def trial : PMF (Fin 3) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (p i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p_nonneg i), p_sum, ENNReal.ofReal_one])

private noncomputable def trials : Measure (ℕ → Fin 3) :=
  Measure.infinitePi fun _ => trial.toMeasure

private instance : IsProbabilityMeasure trials := by
  unfold trials
  infer_instance

private noncomputable def C : Matrix (Fin 3) (Fin 3) ℝ := diagonal p - vecMulVec p p

private theorem trialLaw (n : ℕ) : trials.map (fun ω => ω n) = trial.toMeasure :=
  Measure.infinitePi_map_eval (fun _ : ℕ => trial.toMeasure) n

private theorem trialProb (i : Fin 3) : trials.real {ω | ω 0 = i} = p i := by
  have h := congrArg (fun μ : Measure (Fin 3) => μ {i}) (trialLaw 0)
  rw [Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton i),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i)] at h
  change trials ((fun ω : ℕ → Fin 3 => ω 0) ⁻¹' {i}) = ENNReal.ofReal (p i) at h
  rw [measureReal_def]
  change (trials ((fun ω : ℕ → Fin 3 => ω 0) ⁻¹' {i})).toReal = p i
  rw [h, ENNReal.toReal_ofReal (p_nonneg i)]

private theorem iidTrials : iIndepFun (fun (n : ℕ) (ω : ℕ → Fin 3) => ω n) trials :=
  iIndepFun_infinitePi (X := fun _ : ℕ => id) fun _ => measurable_id

private theorem identTrials (n : ℕ) :
    IdentDistrib (fun ω => ω n) (fun ω => ω 0) trials trials :=
  ⟨(measurable_pi_apply n).aemeasurable, (measurable_pi_apply 0).aemeasurable,
    (trialLaw n).trans (trialLaw 0).symm⟩

-- Realize nondegenerate i.i.d. trials with a third, impossible category.
example :
    (let X := fun (n : ℕ) (ω : ℕ → Fin 3) => EuclideanSpace.basisFun (Fin 3) ℝ (ω n)
     TendstoInDistribution
       (fun (n : ℕ) ω => √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ k ∈ range n, X k ω - WithLp.toLp 2 p))
       atTop id (fun _ => trials) (multivariateGaussian 0 C)) ∧
    cov[fun ω => (EuclideanSpace.basisFun (Fin 3) ℝ (ω 0)) 0,
      fun ω => (EuclideanSpace.basisFun (Fin 3) ℝ (ω 0)) 1; trials] = -1 / 4 ∧
    ¬IsUnit C ∧
    (multivariateGaussian 0 C).map (fun x => x 2) = Measure.dirac 0 := by
  have h := multinomial_proportions_clt (fun (n : ℕ) (ω : ℕ → Fin 3) => ω n) p
    p_sum trialProb iidTrials identTrials
  refine ⟨h.2.2.2.2.2.1, ?_, h.2.2.2.2.1, h.2.2.2.2.2.2 2 (by simp [p])⟩
  rw [h.2.1 0 1]
  change C 0 1 = -1 / 4
  norm_num [C, p, Matrix.vecMulVec_apply]

end MultinomialProportionsCLTTest
