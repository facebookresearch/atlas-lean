/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.BOLTLMMVariational

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open MathlibExt.Biology.StatisticalGenetics.BOLTLMMVariational
open scoped ENNReal NNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.BOLTLMMVariational

/-! ### Non-vacuity: the BOLT-LMM prior and an admissible factor -/

/-- The equal-weight mixture of `N(0, 1)` and `N(0, 1/100)` is a probability measure with a
finite second moment. -/
example : IsProbabilityMeasure (mixturePrior (1 / 2) 1 (1 / 100)) :=
  isProbabilityMeasure_mixturePrior (by norm_num) _ _

example : Integrable (fun b : ℝ => b ^ 2) (mixturePrior (1 / 2) 1 (1 / 100)) :=
  integrable_sq_mixturePrior _ _ _

/-- Boundary `v₂ = 0`: the spike-and-slab prior, a slab plus a point mass at `0`. -/
example (p v : ℝ≥0) :
    mixturePrior p v 0 = (p : ℝ≥0∞) • gaussianReal 0 v + ((1 - p : ℝ≥0) : ℝ≥0∞) • .dirac 0 := by
  simp [mixturePrior]

/-- The prior itself is an admissible factor (zero divergence). -/
lemma isAdmissible_self (π : Measure ℝ) [IsProbabilityMeasure π]
    (h2 : Integrable (fun b : ℝ => b ^ 2) π) : IsAdmissible π π :=
  ⟨inferInstance, h2, Measure.AbsolutelyContinuous.rfl,
    (integrable_zero ℝ ℝ π).congr (llr_self π).symm⟩

/-! ### A one-SNP instance -/

/-- One individual with phenotype `2` and genotype `1`. -/
def X₁ : Matrix (Fin 1) (Fin 1) ℝ := !![1]

/-- With no other SNPs the residual is the phenotype, and the CAVI potential is the Gaussian
log-likelihood `2 b - b² / 2` up to a constant. -/
example (q : Fin 1 → Measure ℝ) (b : ℝ) : potential X₁ ![2] 1 q 0 b = 2 * b - b ^ 2 / 2 := by
  simp [potential, partialResidual, colNormSq, X₁]
  ring

/-- Coordinate ascent from the prior is monotone, for the one-SNP instance with the BOLT-LMM
prior. -/
example (s : ℕ → Fin 1) :
    Monotone fun t => elbo X₁ ![2] 1 (mixturePrior (1 / 2) 1 (1 / 100))
      (caviRun X₁ ![2] 1 (mixturePrior (1 / 2) 1 (1 / 100))
        (fun _ => mixturePrior (1 / 2) 1 (1 / 100)) s t) := by
  have := isProbabilityMeasure_mixturePrior (p := 1 / 2) (by norm_num) 1 (1 / 100)
  exact monotone_elbo_caviRun (integrable_sq_mixturePrior _ _ _) one_pos
    (fun _ => isAdmissible_self _ (integrable_sq_mixturePrior _ _ _)) s

/-! ### Boundary: an inadmissible factor -/

/-- A point mass is not absolutely continuous with respect to a Gaussian prior, so its
divergence is infinite; `elbo` would read it as `0` through `toReal`, which is why every result
assumes admissibility. -/
example : (klDiv (Measure.dirac (1 : ℝ)) (gaussianReal 0 1)).toReal = 0 := by
  have hac : ¬ Measure.dirac (1 : ℝ) ≪ gaussianReal 0 1 := by
    intro h
    have h0 : gaussianReal 0 1 {1} = 0 :=
      gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton
    have h1 := h h0
    simp at h1
  simp [klDiv_of_not_ac hac]

end MathlibExtTest.Biology.StatisticalGenetics.BOLTLMMVariational
