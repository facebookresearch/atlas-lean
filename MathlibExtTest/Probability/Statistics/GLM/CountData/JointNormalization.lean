/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.CountData.JointNormalization

@[expose] public section

open Finset Real
open MathlibExt.Probability.Statistics.GLM.CountData

namespace MathlibExtTest.Probability.Statistics.GLM.CountData.JointNormalization

/-! ### A two-gene, three-sample model -/

/-- Gene `0` Poisson, gene `1` negative binomial with shape `2`; samples `0, 1` replicate
condition `0` and sample `2` is condition `1` with library size `0`; rates `1` and `3`. -/
noncomputable def ex : CountModel (Fin 2) (Fin 3) (Fin 2) where
  law := ![CountLaw.poisson, CountLaw.negBinomial 2]
  condition := ![0, 0, 1]
  librarySize := ![1, 2, 0]
  rate := fun _ c => ![1, 3] c

theorem ex_valid : ex.Valid where
  law_valid := fun g => by fin_cases g <;> simp [ex, CountLaw.Valid]
  librarySize_nonneg := fun j => by fin_cases j <;> norm_num [ex]
  rate_pos := fun _ c => by fin_cases c <;> norm_num [ex]

/-- Joint normalization: the likelihood is a probability mass function on `Fin 2 → Fin 3 → ℕ`,
a zero library size (sample `2`) included. -/
example : HasSum ex.likelihood 1 := CountModel.hasSum_likelihood ex_valid

example : ∑' Y : Fin 2 → Fin 3 → ℕ, ex.likelihood Y = 1 := CountModel.tsum_likelihood ex_valid

/-- The entry `(0, 0)` marginal of the joint law, computed from the definitions: the Poisson
gene in sample `0` (library size `1`, rate `1`) has `P(0) = e^{-1}`. -/
example : ∑' Y : Fin 2 → Fin 3 → ℕ, (if Y 0 0 = 0 then ex.likelihood Y else 0) = exp (-1) := by
  rw [CountModel.tsum_likelihood_entry ex_valid, CountModel.countPMF,
    show ex.mean 0 0 = 1 by norm_num [ex, CountModel.mean],
    show ex.law 0 = CountLaw.poisson from rfl, CountLaw.pmf_poisson_zero zero_le_one]

/-- The entry `(1, 1)` marginal: the negative binomial gene with shape `2` in sample `1`
(library size `2`, rate `1`, mean `2`) has `P(0) = (2 / 4) ^ 2 = 1 / 4`. -/
example : ∑' Y : Fin 2 → Fin 3 → ℕ, (if Y 1 1 = 0 then ex.likelihood Y else 0) = 1 / 4 := by
  rw [CountModel.tsum_likelihood_entry ex_valid, CountModel.countPMF,
    show ex.mean 1 1 = 2 by norm_num [ex, CountModel.mean],
    show ex.law 1 = CountLaw.negBinomial 2 from rfl, CountLaw.pmf_negBinomial_zero]
  norm_num

/-- Identifiability in use: any valid model with the same joint law and the same library size
`2` in sample `1` has rate `1` for gene `1` in sample `1`'s condition, and the same law of gene
`1`. -/
example (M' : CountModel (Fin 2) (Fin 3) (Fin 2)) (hM' : M'.Valid)
    (h : ex.likelihood = M'.likelihood) (hs : M'.librarySize 1 = 2) :
    M'.rate 1 (M'.condition 1) = 1 ∧ M'.law 1 = CountLaw.negBinomial 2 := by
  constructor
  · rw [← CountModel.rate_eq_of_likelihood_eq ex_valid hM' h 1 (by simp [ex, hs])
      (by norm_num [ex])]
    simp [ex]
  · rw [← CountModel.law_eq_of_likelihood_eq ex_valid hM' h 1 (j := 1) (by norm_num [ex])]
    rfl

/-! ### A one-entry model: the joint law from the definitions -/

/-- One gene, one sample: Poisson with library size `1` and rate `1`. -/
noncomputable def one : CountModel Unit Unit Unit where
  law := fun _ => CountLaw.poisson
  condition := id
  librarySize := fun _ => 1
  rate := fun _ _ => 1

theorem one_valid : one.Valid where
  law_valid := fun _ => trivial
  librarySize_nonneg := fun _ => zero_le_one
  rate_pos := fun _ _ => one_pos

/-- The likelihood of the one-entry matrix with count `k` is the Poisson mass `e^{-1} / k!`. -/
theorem one_likelihood (Y : Unit → Unit → ℕ) :
    one.likelihood Y = exp (-1) / (Y () ()).factorial := by
  simp [CountModel.likelihood, CountModel.countPMF, CountModel.mean, one,
    CountLaw.pmf_poisson zero_le_one]

/-- Joint normalization for the one-entry model is `∑ₖ e^{-1} / k! = 1`. -/
example : ∑' Y : Unit → Unit → ℕ, exp (-1) / ((Y () ()).factorial : ℝ) = 1 := by
  simpa [one_likelihood] using CountModel.tsum_likelihood one_valid

/-! ### Boundary cases: the hypotheses of the identifiability results are needed -/

/-- **Known library sizes are needed.** Rescaling by `2` (library size `2`, rate `1 / 2`) gives
the same joint law with a different rate. -/
example : (one.rescale 2).likelihood = one.likelihood ∧
    (one.rescale 2).rate () () ≠ one.rate () () := by
  refine ⟨CountModel.likelihood_rescale one two_ne_zero, ?_⟩
  norm_num [CountModel.rescale, one]

example : (one.rescale 2).Valid := CountModel.valid_rescale one_valid two_pos

/-- **A nonzero library size is needed.** With library size `0`, rates `1` and `2` give the same
joint law. -/
noncomputable def zeroLib (r : ℝ) : CountModel Unit Unit Unit where
  law := fun _ => CountLaw.poisson
  condition := id
  librarySize := fun _ => 0
  rate := fun _ _ => r

theorem zeroLib_valid {r : ℝ} (hr : 0 < r) : (zeroLib r).Valid where
  law_valid := fun _ => trivial
  librarySize_nonneg := fun _ => le_rfl
  rate_pos := fun _ _ => hr

example : (zeroLib 1).likelihood = (zeroLib 2).likelihood ∧
    (zeroLib 1).rate () () ≠ (zeroLib 2).rate () () := by
  refine ⟨funext fun Y => ?_, by norm_num [zeroLib]⟩
  simp only [CountModel.likelihood, Finset.univ_unique, Finset.prod_singleton]
  rw [CountModel.countPMF_eq_of_librarySize_eq_zero (zeroLib_valid one_pos)
    (zeroLib_valid two_pos) () rfl rfl]

/-- **At least one sample is needed.** With no samples the joint law is the point mass at the
empty matrix, whatever the laws: the likelihood is `1`. -/
noncomputable def noSample (L : CountLaw) : CountModel Unit Empty Unit where
  law := fun _ => L
  condition := fun _ => ()
  librarySize := fun _ => 1
  rate := fun _ _ => 1

example (Y : Unit → Empty → ℕ) : (noSample CountLaw.poisson).likelihood Y = 1 := by
  simp [CountModel.likelihood]

example : (noSample CountLaw.poisson).likelihood = (noSample (CountLaw.negBinomial 1)).likelihood ∧
    (noSample CountLaw.poisson).law () ≠ (noSample (CountLaw.negBinomial 1)).law () :=
  ⟨funext fun _ => by simp [CountModel.likelihood], by simp [noSample]⟩

/-- **Every condition needs a replicate.** Condition `false` has no samples, so its rate (`1`
versus `2`) does not affect the joint law, yet the models differ. -/
noncomputable def unobserved (r : ℝ) : CountModel Unit Unit Bool where
  law := fun _ => CountLaw.poisson
  condition := fun _ => true
  librarySize := fun _ => 1
  rate := fun _ c => if c then 1 else r

example : (unobserved 1).likelihood = (unobserved 2).likelihood ∧
    unobserved 1 ≠ unobserved 2 := by
  refine ⟨funext fun Y => by simp [CountModel.likelihood, CountModel.countPMF,
    CountModel.mean, unobserved], fun h => ?_⟩
  have := congrFun (congrFun (congrArg CountModel.rate h) ()) false
  norm_num [unobserved] at this

/-! ### Laws from dispersions -/

/-- Distinct valid laws have distinct dispersions: Poisson `0` versus shape `2`, i.e. `1 / 2`. -/
example : CountLaw.poisson.dispersion ≠ (CountLaw.negBinomial 2).dispersion := by
  simp

example {θ : ℝ} (h : (CountLaw.negBinomial θ).dispersion = (CountLaw.negBinomial 2).dispersion) :
    CountLaw.negBinomial θ = CountLaw.negBinomial 2 := by
  by_cases hθ : 0 < θ
  · exact CountLaw.eq_of_dispersion_eq hθ two_pos h
  · simp only [CountLaw.dispersion_negBinomial, inv_inj] at h
    exact absurd (h ▸ two_pos) hθ

/-! ### Joint identifiability with a known design -/

/-- With the design of `one` known, equal joint laws force the model to be `one`. -/
example (M' : CountModel Unit Unit Unit) (hM' : M'.Valid) (hc : M'.condition = id)
    (hs : M'.librarySize = fun _ => 1) (h : one.likelihood = M'.likelihood) : M' = one :=
  (CountModel.eq_of_likelihood_eq one_valid hM' hc.symm Function.surjective_id hs.symm
    (fun _ => one_pos) h).symm

end MathlibExtTest.Probability.Statistics.GLM.CountData.JointNormalization
