/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.FineMapping

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open MathlibExt.Biology.StatisticalGenetics.FineMapping
open scoped NNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.FineMapping

/-! ### Wakefield's ABF -/

/-- A zero prior variance makes the alternative the null: `ABF = 1`. -/
example {V : ℝ≥0} (hV : V ≠ 0) (b : ℝ) : wakefieldABF V 0 b = 1 := by
  rw [wakefieldABF, add_zero, div_self (gaussianPDFReal_pos _ _ _ hV).ne']

/-- At `z = 0` the ABF is the shrinkage factor `√(V / (V + W))`, here `√(1 / 2)`. -/
example : wakefieldABF 1 1 0 = √(1 / 2) := by
  rw [wakefieldABF_eq one_ne_zero]
  norm_num

/-- Outside the domain (`V = 0`) the definition is Lean's junk value `0`. -/
example (W : ℝ≥0) (b : ℝ) : wakefieldABF 0 W b = 0 := by
  simp [wakefieldABF, gaussianPDFReal_zero_var]

/-! ### Single-effect regression -/

/-- A normalized, non-negative prior on two variants. -/
noncomputable def uniformPrior : PriorWeights (Fin 2) where
  weight := ![1 / 2, 1 / 2]
  weight_nonneg := by intro j; fin_cases j <;> norm_num
  sum_weight := by simp [Fin.sum_univ_two]; norm_num

/-- Posterior inclusion probabilities with a uniform prior are proportional to the Bayes
factors. -/
example : pip uniformPrior ![1, 3] 1 = 3 / 4 := by
  simp [pip, normalizedWeightedEvidence, uniformPrior, Fin.sum_univ_two]
  norm_num

/-- Positive Bayes factors give positive evidence under a valid prior. -/
example : 0 < ∑ j, uniformPrior.weight j * ![1, 3] j := by
  apply PriorWeights.evidence_pos
  intro j
  fin_cases j <;> norm_num

/-- Posterior inclusion probabilities are non-negative. -/
example (j : Fin 2) : 0 ≤ pip uniformPrior ![1, 3] j := by
  apply pip_nonneg
  intro k
  fin_cases k <;> norm_num

/-- Posterior inclusion probabilities sum to one. -/
example : ∑ j, pip uniformPrior ![1, 3] j = 1 := by
  apply sum_pip
  intro j
  fin_cases j <;> norm_num

/-- The singleton prior is the boundary case: its sole posterior probability is one. -/
noncomputable def singletonPrior : PriorWeights (Fin 1) where
  weight := ![1]
  weight_nonneg := by simp
  sum_weight := by simp

example : pip singletonPrior ![7] 0 = 1 := by
  simp [pip, normalizedWeightedEvidence, singletonPrior]

/-- Signed weights cannot inhabit the probability-domain prior API. -/
example : ¬∃ w : PriorWeights (Fin 2), w.weight = ![1, -1] := by
  rintro ⟨w, hw⟩
  have h := w.weight_nonneg 1
  rw [hw] at h
  norm_num at h

/-- Identically zero weights cannot inhabit the probability-domain prior API. -/
example : ¬∃ w : PriorWeights (Fin 2), w.weight = 0 := by
  rintro ⟨w, hw⟩
  have h := w.sum_weight
  simp [hw] at h

/-- The least-squares estimate of `y = x` on `x ≠ 0` is `1`. -/
example {n : Type*} [Fintype n] {x : EuclideanSpace ℝ n} (hx : x ≠ 0) : olsEffect x x = 1 := by
  rw [olsEffect, real_inner_self_eq_norm_sq, div_self (by positivity)]

/-- Outside the domain (`x = 0`) the estimate is Lean's junk value `0`. -/
example {n : Type*} [Fintype n] (y : EuclideanSpace ℝ n) : olsEffect 0 y = 0 := by
  simp [olsEffect]

/-- The covariance of the single-effect model is positive definite for `σ² > 0`. -/
example (x : EuclideanSpace ℝ (Fin 3)) : (serCov 1 2 x).PosDef :=
  posDef_serCov one_ne_zero 2 x

/-! ### coloc -/

/-- **Non-vacuity witness** for `ColocPrior`: the default priors of the coloc package,
`p1 = p2 = 10⁻⁴` and `p12 = 10⁻⁵`, on two variants. -/
noncomputable def defaultPrior : ColocPrior (Fin 2) where
  p1 := 1 / 10 ^ 4
  p2 := 1 / 10 ^ 4
  p12 := 1 / 10 ^ 5
  p1_nonneg := by norm_num
  p2_nonneg := by norm_num
  p12_nonneg := by norm_num
  sum_le_one := by simp; norm_num

/-- The review's one-variant edge case. -/
noncomputable def oneVariantPrior : ColocPrior (Fin 1) where
  p1 := 0
  p2 := 0
  p12 := 1 / 2
  p1_nonneg := by norm_num
  p2_nonneg := by norm_num
  p12_nonneg := by norm_num
  sum_le_one := by simp; norm_num

/-- The parent's finite signed-BF boundary probe. -/
noncomputable def signedBFProbePrior : ColocPrior (Fin 1) where
  p1 := 1
  p2 := 0
  p12 := 0
  p1_nonneg := by norm_num
  p2_nonneg := by norm_num
  p12_nonneg := by norm_num
  sum_le_one := by simp

example : colocHypothesis ((some 0, some 0) : Option (Fin 2) × Option (Fin 2)) = .h4 := rfl

example : colocHypothesis ((some 0, some 1) : Option (Fin 2) × Option (Fin 2)) = .h3 := rfl

/-- With all Bayes factors equal to `1`, the H4 closed form is `p12` times the number of
variants. -/
example : colocClosedForm defaultPrior 1 1 .h4 = 2 / 10 ^ 5 := by
  simp [colocClosedForm, defaultPrior]
  norm_num

/-- The cited coloc H0 configuration weight is one. -/
example : colocClosedForm oneVariantPrior 1 1 .h0 = 1 := by
  simp [colocClosedForm]

/-- In the review's example, the cited H0 posterior is `1 / (1 + 1/2) = 2/3`. -/
example : colocClosedForm oneVariantPrior 1 1 .h0 /
    ∑ h, colocClosedForm oneVariantPrior 1 1 h = 2 / 3 := by
  rw [show (Finset.univ : Finset ColocHypothesis) = {.h0, .h1, .h2, .h3, .h4} from rfl]
  simp [colocClosedForm, oneVariantPrior]
  norm_num

/-- Outside the probability domain, the raw algebraic H0 ratio can be `2`. -/
example : colocClosedForm signedBFProbePrior ![-1 / 2] ![1] .h0 /
    ∑ h, colocClosedForm signedBFProbePrior ![-1 / 2] ![1] h = 2 := by
  rw [show (Finset.univ : Finset ColocHypothesis) = {.h0, .h1, .h2, .h3, .h4} from rfl]
  simp [colocClosedForm, signedBFProbePrior]
  norm_num

/-- Outside the probability domain, the raw algebraic H1 ratio can be `-1`. -/
example : colocClosedForm signedBFProbePrior ![-1 / 2] ![1] .h1 /
    ∑ h, colocClosedForm signedBFProbePrior ![-1 / 2] ![1] h = -1 := by
  rw [show (Finset.univ : Finset ColocHypothesis) = {.h0, .h1, .h2, .h3, .h4} from rfl]
  simp [colocClosedForm, signedBFProbePrior]
  norm_num

/-- Non-negative Bayes factors give strictly positive coloc evidence, including zero factors. -/
example : 0 < ∑ h, colocClosedForm defaultPrior ![0, 2] ![3, 0] h := by
  apply colocEvidence_pos
  · intro j
    fin_cases j <;> norm_num
  · intro j
    fin_cases j <;> norm_num

/-- Normalized coloc hypothesis weights are non-negative on the Bayes-factor domain. -/
example (h : ColocHypothesis) :
    0 ≤ colocClosedForm defaultPrior ![0, 2] ![3, 0] h /
      ∑ h', colocClosedForm defaultPrior ![0, 2] ![3, 0] h' := by
  apply colocPosterior_nonneg
  · intro j
    fin_cases j <;> norm_num
  · intro j
    fin_cases j <;> norm_num

/-- Normalized coloc hypothesis weights sum to one on the Bayes-factor domain. -/
example : ∑ h, colocClosedForm defaultPrior ![0, 2] ![3, 0] h /
    ∑ h', colocClosedForm defaultPrior ![0, 2] ![3, 0] h' = 1 := by
  apply sum_colocPosterior_eq_one
  · intro j
    fin_cases j <;> norm_num
  · intro j
    fin_cases j <;> norm_num

/-- The optional categorical configuration priors retain their normalized interpretation. -/
example : ∑ S, defaultPrior.categoricalPrior S = 1 := defaultPrior.sum_categoricalPrior

/-- The H3 sum by brute force, for two variants with Bayes factors `(2, 3)` and `(5, 7)`:
`p1 p2 (2 · 7 + 3 · 5)`. -/
example : ∑ S ∈ Finset.univ.filter (fun S => colocHypothesis S = .h3),
    defaultPrior.weight S * colocBF ![2, 3] ![5, 7] S = 29 / 10 ^ 8 := by
  rw [sum_colocWeight_mul_colocBF]
  simp [colocClosedForm, defaultPrior, Fin.sum_univ_two]
  norm_num

/-! ### Credible sets -/

/-- Inclusion probabilities `(0.5, 0.3, 0.2)`, already sorted. -/
noncomputable def α3 : Fin 3 → ℝ := ![1 / 2, 3 / 10, 1 / 5]

/-- The identity order, viewed as an enumeration of `Fin 3` by `Fin (card (Fin 3))`. -/
def σ3 : Fin (Fintype.card (Fin 3)) ≃ Fin 3 := finCongr (Fintype.card_fin 3)

theorem antitone_α3 : Antitone (α3 ∘ σ3) := by
  refine Antitone.comp_monotone ?_ fun i j h => h
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [α3, Fin.le_def] <;> norm_num

/-- `{0, 1}` is a `0.8`-credible set. -/
example : IsCredibleSet α3 (4 / 5) {0, 1} := by
  simp [IsCredibleSet, α3]
  norm_num

/-- Every `0.8`-credible set has at least two variants, since no prefix of length `< 2` has
mass `0.8`. -/
example (S : Finset (Fin 3)) (hS : IsCredibleSet α3 (4 / 5) S) : 2 ≤ S.card := by
  refine le_card_of_isCredibleSet α3 antitone_α3 (fun m hm => ?_) hS
  interval_cases m
  · simp [IsCredibleSet, sortedPrefix]
  · rw [show sortedPrefix σ3 1 = {0} by decide]
    simp [IsCredibleSet, α3]
    norm_num

#print axioms wakefieldABF_eq
#print axioms rnDeriv_map_add_ae_eq
#print axioms multivariateGaussianPDFReal_serCov_div
#print axioms serLikelihoodRatio_eq_normalizedWeightedEvidence
#print axioms serPosterior_evidence_pos
#print axioms serPosterior_eq_pip
#print axioms sum_pip
#print axioms condDistrib_ser_effect
#print axioms sum_colocWeight_mul_colocBF
#print axioms colocBF_nonneg
#print axioms colocClosedForm_nonneg
#print axioms colocEvidence_pos
#print axioms colocPosterior_nonneg
#print axioms sum_colocPosterior_eq_one
#print axioms ColocPrior.sum_categoricalPrior
#print axioms colocCategoricalPosterior_eq
#print axioms exists_minimal_credible_prefix

end MathlibExtTest.Biology.StatisticalGenetics.FineMapping
