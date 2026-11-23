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

/-- Variance of a function of one product coordinate is the variance under that
coordinate law, by marginalization of the mean and the squared deviation
(`MeasureTheory.integral_comp_eval`). -/
private theorem variance_pi_coordinate {B : Type*} [Fintype B]
    {E : B → Type*} [(b : B) → MeasurableSpace (E b)]
    (μs : (b : B) → Measure (E b)) [∀ b, IsProbabilityMeasure (μs b)]
    (b₀ : B) {g : E b₀ → ℝ} (hg : Measurable g) :
    ProbabilityTheory.variance (fun x => g (x b₀)) (Measure.pi μs) =
      ProbabilityTheory.variance g (μs b₀) := by
  have hX : Measurable (fun x : (b : B) → E b => g (x b₀)) :=
    hg.comp (measurable_pi_apply b₀)
  have hmean : (∫ x, g (x b₀) ∂(Measure.pi μs)) = ∫ y, g y ∂(μs b₀) :=
    MeasureTheory.integral_comp_eval hg.aestronglyMeasurable
  rw [ProbabilityTheory.variance_eq_integral hX.aemeasurable,
    ProbabilityTheory.variance_eq_integral hg.aemeasurable]
  change (∫ x, (g (x b₀) - ∫ x, g (x b₀) ∂(Measure.pi μs)) ^ 2 ∂(Measure.pi μs)) =
    ∫ y, (g y - ∫ y, g y ∂(μs b₀)) ^ 2 ∂(μs b₀)
  rw [hmean]
  exact MeasureTheory.integral_comp_eval
    (((hg.sub_const _).pow_const 2).aestronglyMeasurable)

/-- Block coordinate statistics are independent under the product law. The
family is stated as `fun b S => g b (S b)` on the product sample space, which
is the shape `iIndepFun` requires (a bare dependent `g` does not elaborate).
Each block law must be a probability measure (`hprob`); the proof is
`ProbabilityTheory.iIndepFun_pi`. -/
private theorem indepFun_blockCoord {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ℕ} (blocks : Fin B → Finset ι)
    (n : Fin B → ℕ) (g : (b : Fin B) → Finset ↥(blocks b) → ℝ)
    (hg : ∀ b, Measurable (g b))
    (hprob : ∀ b, IsProbabilityMeasure (completeRandomization ↥(blocks b) (n b))) :
    ProbabilityTheory.iIndepFun (fun b S => g b (S b))
      (blockRandomization B blocks n) := by
  have := hprob
  unfold blockRandomization
  exact ProbabilityTheory.iIndepFun_pi (fun b => (hg b).aemeasurable)

/-- Weighted Neyman estimator for the blocked design: squared weights times
per-block `neymanVar`. -/
noncomputable def blockNeyman {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y₀ y₁ : ι → ℝ) {B : ℕ} (blocks : Fin B → Finset ι)
    (S : ∀ b, Finset ↥(blocks b)) : ℝ :=
  ∑ b, (((blocks b).card : ℝ) / Fintype.card ι) ^ 2 *
    neymanVar (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) (S b)

/-- Variance of the weighted block contrast under independent complete
randomization within each block: it is the sum over blocks of the squared
weight `((blocks b).card / N) ^ 2` (`N = Fintype.card ι`) times that block's
exact Neyman variance `popVar y₁ / n b + popVar y₀ / ((blocks b).card - n b) -
popVar (y₁ - y₀) / (blocks b).card`, with population variances taken on the
block subtype. Each block needs at least one treated and one control unit
(`h₁`, `h₀`); no disjointness or coverage assumption on the blocks is
required. -/
theorem variance_blockContrast {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y₀ y₁ : ι → ℝ) {B : ℕ}
    (blocks : Fin B → Finset ι) (n : Fin B → ℕ)
    (h₁ : ∀ b, 1 ≤ n b) (h₀ : ∀ b, n b + 1 ≤ (blocks b).card) :
    ProbabilityTheory.variance (blockContrast y₀ y₁ blocks)
        (blockRandomization B blocks n) =
      ∑ b, (((blocks b).card : ℝ) / Fintype.card ι) ^ 2 *
        (popVar ((y₁ ∘ Subtype.val : ↥(blocks b) → ℝ)) / (n b : ℝ) +
          popVar ((y₀ ∘ Subtype.val : ↥(blocks b) → ℝ)) /
            (((blocks b).card : ℝ) - (n b : ℝ)) -
          popVar (fun i : ↥(blocks b) => y₁ i - y₀ i) /
            ((blocks b).card : ℝ)) := by
  have hprob : ∀ b, IsProbabilityMeasure
      (completeRandomization ↥(blocks b) (n b)) := fun b =>
    isProbabilityMeasure_completeRandomization (by
      rw [Fintype.card_coe]
      have h0b := h₀ b
      omega)
  have : IsProbabilityMeasure (blockRandomization B blocks n) := by
    unfold blockRandomization
    infer_instance
  have hindep : ProbabilityTheory.iIndepFun
      (fun (b : Fin B) (S : ∀ b, Finset ↥(blocks b)) =>
        (((blocks b).card : ℝ) / Fintype.card ι) *
          diffInMeans (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) (S b))
      (blockRandomization B blocks n) :=
    indepFun_blockCoord blocks n
      (fun b T => (((blocks b).card : ℝ) / Fintype.card ι) *
        diffInMeans (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) T)
      (fun b => (measurable_of_countable _).const_mul _) hprob
  have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin B)) : Set (Fin B))
      (fun i j => ProbabilityTheory.IndepFun
        (fun S : ∀ b, Finset ↥(blocks b) =>
          (((blocks i).card : ℝ) / Fintype.card ι) *
            diffInMeans (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) (S i))
        (fun S : ∀ b, Finset ↥(blocks b) =>
          (((blocks j).card : ℝ) / Fintype.card ι) *
            diffInMeans (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) (S j))
        (blockRandomization B blocks n)) :=
    fun i _ j _ hij => hindep.indepFun hij
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin B)), MemLp
      (fun S : ∀ b, Finset ↥(blocks b) =>
        (((blocks i).card : ℝ) / Fintype.card ι) *
          diffInMeans (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) (S i))
      2 (blockRandomization B blocks n) :=
    fun i _ => MemLp.of_discrete
  have hvarsum := ProbabilityTheory.IndepFun.variance_sum hmem hpair
  have hfun : blockContrast y₀ y₁ blocks =
      ∑ i ∈ (Finset.univ : Finset (Fin B)), fun S : ∀ b, Finset ↥(blocks b) =>
        (((blocks i).card : ℝ) / Fintype.card ι) *
          diffInMeans (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) (S i) := by
    funext S
    simp only [Finset.sum_apply]
    unfold blockContrast
    rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hvar : ∀ b : Fin B, ProbabilityTheory.variance
      (fun S : ∀ b, Finset ↥(blocks b) =>
        (((blocks b).card : ℝ) / Fintype.card ι) *
          diffInMeans (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) (S b))
      (blockRandomization B blocks n) =
      (((blocks b).card : ℝ) / Fintype.card ι) ^ 2 *
        (popVar ((y₁ ∘ Subtype.val : ↥(blocks b) → ℝ)) / (n b : ℝ) +
          popVar ((y₀ ∘ Subtype.val : ↥(blocks b) → ℝ)) /
            (((blocks b).card : ℝ) - (n b : ℝ)) -
          popVar (fun i : ↥(blocks b) => y₁ i - y₀ i) /
            ((blocks b).card : ℝ)) := fun b => by
    have hbound : n b + 1 ≤ Fintype.card ↥(blocks b) := by
      rw [Fintype.card_coe]
      exact h₀ b
    have hmain : ProbabilityTheory.variance
        (diffInMeans (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val))
        (completeRandomization ↥(blocks b) (n b)) =
        popVar ((y₁ ∘ Subtype.val : ↥(blocks b) → ℝ)) / (n b : ℝ) +
          popVar ((y₀ ∘ Subtype.val : ↥(blocks b) → ℝ)) /
            (((blocks b).card : ℝ) - (n b : ℝ)) -
          popVar (fun i : ↥(blocks b) => y₁ i - y₀ i) /
            ((blocks b).card : ℝ) := by
      have h := variance_diffInMeans_completeRandomization (y₀ ∘ Subtype.val)
        (y₁ ∘ Subtype.val) (h₁ b) hbound
      rwa [Fintype.card_coe] at h
    have hcoord : ProbabilityTheory.variance
        (fun S : ∀ b, Finset ↥(blocks b) =>
          diffInMeans (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) (S b))
        (blockRandomization B blocks n) =
        ProbabilityTheory.variance
          (diffInMeans (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val))
          (completeRandomization ↥(blocks b) (n b)) := by
      change ProbabilityTheory.variance (fun S => diffInMeans _ _ (S b))
        (Measure.pi fun b => completeRandomization ↥(blocks b) (n b)) = _
      exact variance_pi_coordinate _ b (measurable_of_countable _)
    rw [ProbabilityTheory.variance_const_mul, hcoord, hmain]
  rw [hfun, hvarsum]
  simp only [hvar]

/-- Expectation of the weighted Neyman estimator under independent complete
randomization within each block: it is the sum over blocks of the squared
weight `((blocks b).card / N) ^ 2` times `popVar y₁ / n b + popVar y₀ /
((blocks b).card - n b)`, with population variances on the block subtype. Each
block needs at least two treated and two control units (`h₁`, `h₀`). -/
theorem integral_blockNeyman {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y₀ y₁ : ι → ℝ) {B : ℕ}
    (blocks : Fin B → Finset ι) (n : Fin B → ℕ)
    (h₁ : ∀ b, 2 ≤ n b) (h₀ : ∀ b, n b + 2 ≤ (blocks b).card) :
    ∫ S, blockNeyman y₀ y₁ blocks S ∂(blockRandomization B blocks n) =
      ∑ b, (((blocks b).card : ℝ) / Fintype.card ι) ^ 2 *
        (popVar ((y₁ ∘ Subtype.val : ↥(blocks b) → ℝ)) / (n b : ℝ) +
          popVar ((y₀ ∘ Subtype.val : ↥(blocks b) → ℝ)) /
            (((blocks b).card : ℝ) - (n b : ℝ))) := by
  have hprob : ∀ b, IsProbabilityMeasure
      (completeRandomization ↥(blocks b) (n b)) := fun b =>
    isProbabilityMeasure_completeRandomization (by
      rw [Fintype.card_coe]
      have h0b := h₀ b
      omega)
  have : IsProbabilityMeasure (blockRandomization B blocks n) := by
    unfold blockRandomization
    infer_instance
  have hblock : ∀ b, (∫ S, (((blocks b).card : ℝ) / Fintype.card ι) ^ 2 *
      neymanVar (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) (S b)
      ∂(blockRandomization B blocks n)) =
      (((blocks b).card : ℝ) / Fintype.card ι) ^ 2 *
        (popVar ((y₁ ∘ Subtype.val : ↥(blocks b) → ℝ)) / (n b : ℝ) +
          popVar ((y₀ ∘ Subtype.val : ↥(blocks b) → ℝ)) /
            (((blocks b).card : ℝ) - (n b : ℝ))) := fun b => by
    have hbound : n b + 2 ≤ Fintype.card ↥(blocks b) := by
      rw [Fintype.card_coe]
      exact h₀ b
    have hNey : (∫ T, neymanVar (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) T
        ∂(completeRandomization ↥(blocks b) (n b))) =
        popVar ((y₁ ∘ Subtype.val : ↥(blocks b) → ℝ)) / (n b : ℝ) +
          popVar ((y₀ ∘ Subtype.val : ↥(blocks b) → ℝ)) /
            (((blocks b).card : ℝ) - (n b : ℝ)) := by
      have h := integral_neymanVar_completeRandomization (y₀ ∘ Subtype.val)
        (y₁ ∘ Subtype.val) (h₁ b) hbound
      rwa [Fintype.card_coe] at h
    have hcoord : (∫ S, neymanVar (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) (S b)
        ∂(blockRandomization B blocks n)) =
        ∫ T, neymanVar (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) T
          ∂(completeRandomization ↥(blocks b) (n b)) := by
      change (∫ S, neymanVar (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) (S b)
        ∂(Measure.pi fun b => completeRandomization ↥(blocks b) (n b))) =
        ∫ T, neymanVar (y₀ ∘ Subtype.val) (y₁ ∘ Subtype.val) T
          ∂(completeRandomization ↥(blocks b) (n b))
      exact MeasureTheory.integral_comp_eval
        (measurable_of_countable _).aestronglyMeasurable
    rw [integral_const_mul, hcoord, hNey]
  unfold blockNeyman
  rw [integral_finsetSum Finset.univ (fun b _ => Integrable.of_finite)]
  simp only [hblock]

end MathlibExt.Probability.Statistics.Experiment
