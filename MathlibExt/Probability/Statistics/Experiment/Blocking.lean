/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Experiment.Assignment
public import MathlibExt.Probability.Causality.CausalIdentification
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Blocked randomization: product assignment laws and weighted contrasts

Independent complete randomization within fixed pre-treatment blocks; the
block-size-weighted observed contrast is unbiased for the population ATE.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open MathlibExt.Probability.Causality

namespace MathlibExt.Probability.Statistics.Experiment

noncomputable def blockRandomization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℕ) (blocks : Fin B → Finset ι) (n : Fin B → ℕ) :
    Measure (∀ b, Finset ↥(blocks b)) :=
  Measure.pi fun b => completeRandomization ↥(blocks b) (n b)

/-- Union of per-block treated sets as a treated set of the full population. -/
noncomputable def blockTreated {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ℕ} (blocks : Fin B → Finset ι) (S : ∀ b, Finset ↥(blocks b)) :
    Finset ι :=
  Finset.univ.biUnion fun b => Finset.image Subtype.val (S b)

/-- Block-size-weighted contrast of per-block differences in means. -/
noncomputable def blockContrast {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y₀ y₁ : ι → ℝ) {B : ℕ} (blocks : Fin B → Finset ι)
    (S : ∀ b, Finset ↥(blocks b)) : ℝ :=
  (∑ b, ((blocks b).card : ℝ) * diffInMeans (y₀ ∘ Subtype.val)
    (y₁ ∘ Subtype.val) (S b)) / Fintype.card ι

/-- The block product law is a probability measure when every block's treated
count fits. Mirrors `isProbabilityMeasure_completeRandomization` per block. -/
theorem isProbabilityMeasure_blockRandomization {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ℕ} (blocks : Fin B → Finset ι) (n : Fin B → ℕ)
    (h : ∀ b, n b ≤ (blocks b).card) :
    IsProbabilityMeasure (blockRandomization B blocks n) := by
  have hprob : ∀ b, IsProbabilityMeasure
      (completeRandomization ↥(blocks b) (n b)) := fun b =>
    isProbabilityMeasure_completeRandomization (by
      rw [Fintype.card_coe]
      have hb := h b
      omega)
  have _hprob := hprob
  unfold blockRandomization
  infer_instance

set_option linter.unusedDecidableInType false in
/-- Marginalization helper: integrating a function of one product coordinate
against a product measure is the integral against that coordinate, by
`MeasureTheory.integral_comp_eval`. Private. -/
private theorem integral_pi_coordinate {B : Type*} [Fintype B] [DecidableEq B]
    {E : B → Type*} [(b : B) → MeasurableSpace (E b)]
    (μs : (b : B) → Measure (E b)) [∀ b, IsProbabilityMeasure (μs b)]
    (b₀ : B) {g : E b₀ → ℝ} (hg : Measurable g) :
    ∫ x, g (x b₀) ∂(Measure.pi μs) = ∫ y, g y ∂(μs b₀) := by
  exact MeasureTheory.integral_comp_eval hg.aestronglyMeasurable

/-- Weighted block contrast is unbiased for the population ATE.
Clause map: fixed pre-treatment partition (`blocks`, disjointness `hdisj`, coverage
`hcover`); independent complete randomization per block (`blockRandomization` with
treated counts `n`); per-block contrast of the treated-set coordinate as `diffInMeans`
(`blockContrast`); block-size weights (`(blocks b).card / N`); both arms in every block
(`h₁`, `h₀`). -/
theorem integral_blockContrast {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y₀ y₁ : ι → ℝ) {B : ℕ} (blocks : Fin B → Finset ι) (n : Fin B → ℕ)
    (hdisj : Pairwise (Function.onFun Disjoint blocks))
    (hcover : Finset.univ.biUnion blocks = Finset.univ)
    (h₁ : ∀ b, 1 ≤ n b) (h₀ : ∀ b, n b + 1 ≤ (blocks b).card) :
    ∫ S, blockContrast y₀ y₁ blocks S ∂(blockRandomization B blocks n) =
      ate y₀ y₁ := by
  have hprob : ∀ b, IsProbabilityMeasure
      (completeRandomization ↥(blocks b) (n b)) := fun b =>
    isProbabilityMeasure_completeRandomization (by
      rw [Fintype.card_coe]
      have h0b := h₀ b
      omega)
  have _hprob := hprob
  have _hprod : IsProbabilityMeasure (blockRandomization B blocks n) :=
    isProbabilityMeasure_blockRandomization blocks n (fun b => by
      have h0b := h₀ b
      omega)
  have hblock : ∀ b, (∫ S, ((blocks b).card : ℝ) * diffInMeans (y₀ ∘ Subtype.val)
      (y₁ ∘ Subtype.val) (S b) ∂(blockRandomization B blocks n)) =
      ∑ i ∈ blocks b, (y₁ i - y₀ i) := fun b => by
    have hbound : n b + 1 ≤ Fintype.card ↥(blocks b) := by
      rw [Fintype.card_coe]
      exact h₀ b
    have hNey : (∫ T, diffInMeans (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) T
        ∂(completeRandomization ↥(blocks b) (n b))) =
        ate (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) :=
      integral_diffInMeans_completeRandomization _ _ (h₁ b) hbound
    have hcoord : (∫ S, diffInMeans (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) (S b)
        ∂(blockRandomization B blocks n)) =
        ∫ T, diffInMeans (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) T
          ∂(completeRandomization ↥(blocks b) (n b)) := by
      change (∫ S, diffInMeans (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) (S b)
        ∂(Measure.pi fun b => completeRandomization ↥(blocks b) (n b))) =
        ∫ T, diffInMeans (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) T
          ∂(completeRandomization ↥(blocks b) (n b))
      exact integral_pi_coordinate _ b (measurable_of_countable _)
    have hcard_ne : ((blocks b).card : ℝ) ≠ 0 := by
      exact_mod_cast (show (blocks b).card ≠ 0 from by
        have h1b := h₁ b
        have h0b := h₀ b
        omega)
    have hsum : (∑ x : ↥(blocks b), ((y₁ ∘ Subtype.val) x - (y₀ ∘ Subtype.val) x)) =
        ∑ i ∈ blocks b, (y₁ i - y₀ i) :=
      Finset.sum_coe_sort (blocks b) (fun i => y₁ i - y₀ i)
    rw [integral_const_mul, hcoord, hNey]
    simp only [ate, popMean, Fintype.card_coe, hsum]
    rw [mul_comm _ _, div_mul_cancel₀ _ hcard_ne]
  have hdisj' : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin B)) : Set (Fin B))
      blocks :=
    fun i _ j _ hij => hdisj hij
  unfold blockContrast
  rw [integral_div, integral_finsetSum Finset.univ (fun b _ => Integrable.of_finite)]
  simp only [hblock]
  rw [← Finset.sum_biUnion hdisj', hcover, ate, popMean]

end MathlibExt.Probability.Statistics.Experiment
