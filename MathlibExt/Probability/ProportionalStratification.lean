/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.HasLaw
public import MathlibExt.Probability.MonteCarloRate

/-!
# Proportional stratification

Given a finite measurable partition, sample independently from the normalized restriction of
`μ` to each cell. The sampling index is a pair `(j, i)` with `i : Fin (k j)`: the number of
draws from each cell is fixed before sampling. In particular the product law gives independence
both within and across cells; it is not the law of an i.i.d. sample from `μ`.

Art B. Owen, *Monte Carlo Theory, Methods and Examples*, chapter 8, §8.4, equations (8.8),
(8.9), (8.12)–(8.14): variance of the stratified mean, within/between decomposition, and
proportional allocation. The equal-budget criterion below is an algebraic consequence for
constant positive costs per draw and exact integer allocations, not a rounding rule.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace MathlibExt.Probability

variable {α J : Type*} [MeasurableSpace α] [Fintype J]

/-- Positive-mass measurable cells of a finite partition, covering the population almost surely. -/
structure Stratification (μ : Measure α) (J : Type*) [Fintype J] where
  cell : J → Set α
  measurableSet_cell : ∀ j, MeasurableSet (cell j)
  disjoint : Pairwise fun i j ↦ Disjoint (cell i) (cell j)
  covers : ∀ᵐ x ∂μ, x ∈ ⋃ j, cell j
  mass_ne_zero : ∀ j, μ (cell j) ≠ 0

namespace Stratification

variable {μ : Measure α} [IsProbabilityMeasure μ] (S : Stratification μ J)

/-- The probability of a cell under the original sampling law. -/
def weight (j : J) : ℝ := μ.real (S.cell j)

lemma weight_pos (j : J) : 0 < S.weight j :=
  ENNReal.toReal_pos (S.mass_ne_zero j) (measure_ne_top _ _)

/-- Integration over the population is a weighted sum of conditional integrals over its cells. -/
theorem integral_eq_sum_cond {g : α → ℝ} (hg : Integrable g μ) :
    μ[g] = ∑ j, S.weight j * (μ[|S.cell j])[g] := by
  calc
    μ[g] = ∫ x in ⋃ j, S.cell j, g x ∂μ := by
      rw [Measure.restrict_eq_self_of_ae_mem S.covers]
    _ = ∑ j, ∫ x in S.cell j, g x ∂μ :=
      integral_iUnion_fintype S.measurableSet_cell S.disjoint (fun _ ↦ hg.integrableOn)
    _ = _ := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
      change _ = S.weight j * ((S.weight j)⁻¹ * _)
      rw [← mul_assoc, mul_inv_cancel₀ (S.weight_pos j).ne', one_mul]

lemma sum_weights : ∑ j, S.weight j = 1 := by
  have (j : J) := cond_isProbabilityMeasure (S.mass_ne_zero j)
  simpa using (S.integral_eq_sum_cond (integrable_const (1 : ℝ))).symm

omit [IsProbabilityMeasure μ] in
lemma memLp_cond {f : α → ℝ} (hf : MemLp f 2 μ) (j : J) : MemLp f 2 μ[|S.cell j] :=
  (hf.restrict _).smul_measure (ENNReal.inv_ne_top.mpr (S.mass_ne_zero j))

/-- The within-stratum component of population variance: the mean of the conditional variances. -/
def withinVariance (f : α → ℝ) : ℝ := ∑ j, S.weight j * Var[f; μ[|S.cell j]]

/-- Total variance is the within-stratum variance plus the weighted squared deviations of
conditional means from the population mean. -/
theorem variance_eq_within_add_between {f : α → ℝ} (hf : MemLp f 2 μ) :
    Var[f; μ] = S.withinVariance f + ∑ j, S.weight j * ((μ[|S.cell j])[f] - μ[f]) ^ 2 := by
  let g := fun x ↦ f x - μ[f]
  have hg : MemLp g 2 μ := hf.sub (memLp_const _)
  rw [variance_eq_integral hf.aemeasurable, S.integral_eq_sum_cond hg.integrable_sq,
    withinVariance, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  let ν := μ[|S.cell j]
  have : IsProbabilityMeasure ν := cond_isProbabilityMeasure (S.mass_ne_zero j)
  have hf' : MemLp f 2 ν := S.memLp_cond hf j
  have hmean : ν[g] = ν[f] - μ[f] := by
    simp [g, integral_sub (hf'.integrable one_le_two) (integrable_const _)]
  have hvar : Var[g; ν] = Var[f; ν] := variance_sub_const hf'.aestronglyMeasurable _
  have hmoment := variance_eq_sub (S.memLp_cond hg j)
  change Var[g; ν] = ν[g ^ 2] - ν[g] ^ 2 at hmoment
  rw [hvar, hmean] at hmoment
  change S.weight j * ν[g ^ 2] = _
  rw [← mul_add, sub_eq_iff_eq_add.mp hmoment.symm]

/-- The independent sampling law, with one conditional-law factor per draw in each cell. -/
def sampleLaw (k : J → ℕ) : Measure ((Σ j, Fin (k j)) → α) :=
  Measure.pi fun t ↦ μ[|S.cell t.1]

/-- Every coordinate has the conditional law of its own cell. -/
theorem measurePreserving_draw (k : J → ℕ) (t : Σ j, Fin (k j)) :
    MeasurePreserving (Function.eval t) (S.sampleLaw k) μ[|S.cell t.1] := by
  let (i : Σ j, Fin (k j)) : IsProbabilityMeasure μ[|S.cell i.1] :=
    cond_isProbabilityMeasure (S.mass_ne_zero _)
  exact measurePreserving_eval (fun i : Σ j, Fin (k j) ↦ μ[|S.cell i.1]) t

/-- The weighted sum of the sample means of the strata. -/
def estimator (f : α → ℝ) (k : J → ℕ) (x : (Σ j, Fin (k j)) → α) : ℝ :=
  ∑ j, S.weight j * ((∑ i, f (x ⟨j, i⟩)) / k j)

/-- With proportional allocation there are exactly `n` draws in the array. -/
theorem card_draws {n : ℕ} {k : J → ℕ} (hk : ∀ j, (k j : ℝ) = n * S.weight j) :
    Fintype.card (Σ j, Fin (k j)) = n := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact_mod_cast (show ∑ j, (k j : ℝ) = n by simp_rw [hk, ← Finset.mul_sum, S.sum_weights, mul_one])

/-- Under exact proportional allocation the weights cancel: the estimator is the unweighted
mean of all the draws, pointwise, without using independence. -/
theorem estimator_eq_mean (f : α → ℝ) {k : J → ℕ} {n : ℕ} (hn : 0 < n)
    (hk : ∀ j, (k j : ℝ) = n * S.weight j) (x : (Σ j, Fin (k j)) → α) :
    S.estimator f k x = (∑ t, f (x t)) / n := by
  rw [estimator, Fintype.sum_sigma, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hk]
  field_simp [(S.weight_pos j).ne', Nat.cast_ne_zero.mpr hn.ne']

/-- The variance for arbitrary positive integer counts, before imposing proportionality. -/
theorem variance_estimator {f : α → ℝ} (hf : MemLp f 2 μ) {k : J → ℕ} (hk : ∀ j, 0 < k j) :
    Var[S.estimator f k; S.sampleLaw k] = ∑ j, S.weight j ^ 2 * Var[f; μ[|S.cell j]] / k j := by
  let a := fun j ↦ S.weight j / k j
  let ν := fun t : Σ j, Fin (k j) ↦ μ[|S.cell t.1]
  let (t : Σ j, Fin (k j)) : IsProbabilityMeasure (ν t) :=
    cond_isProbabilityMeasure (S.mass_ne_zero _)
  have he : S.estimator f k = ∑ t : Σ j, Fin (k j), fun x ↦ a t.1 * f (x t) := by
    funext x
    simp only [estimator, Finset.sum_apply, Fintype.sum_sigma, ← Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by dsimp [a]; ring
  rw [he, sampleLaw, variance_sum_pi (μ := ν) (X := fun t x ↦ a t.1 * f x)
    (fun t ↦ (S.memLp_cond hf t.1).const_mul _), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [ν, variance_const_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, a]
  field_simp [Nat.cast_ne_zero.mpr (hk j).ne']

/-- Under proportional allocation the independent stratified estimator has variance `σ_W² / n`. -/
theorem variance_proportional {f : α → ℝ} (hf : MemLp f 2 μ) {k : J → ℕ} {n : ℕ}
    (hn : 0 < n) (hk : ∀ j, (k j : ℝ) = n * S.weight j) :
    Var[S.estimator f k; S.sampleLaw k] = S.withinVariance f / n := by
  have hk' (j : J) : 0 < k j := by
    have h : 0 < (k j : ℝ) := by rw [hk]; exact mul_pos (Nat.cast_pos.mpr hn) (S.weight_pos j)
    exact_mod_cast h
  rw [S.variance_estimator hf hk', withinVariance, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hk]
  field_simp [(S.weight_pos j).ne', Nat.cast_ne_zero.mpr hn.ne']

/-- The same variance formula on any sample space: the draws have their respective conditional
laws and the entire family (both within and across strata) is independent. -/
theorem variance_proportional_of_indep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : α → ℝ} (hf : MemLp f 2 μ) {k : J → ℕ} {n : ℕ} (hn : 0 < n)
    (hk : ∀ j, (k j : ℝ) = n * S.weight j) {X : (Σ j, Fin (k j)) → Ω → α}
    (hX : ∀ t, HasLaw (X t) μ[|S.cell t.1] P) (hi : iIndepFun X P) :
    Var[fun ω ↦ S.estimator f k (fun t ↦ X t ω); P] = S.withinVariance f / n := by
  have hjoint : HasLaw (fun ω t ↦ X t ω) (S.sampleLaw k) P := hi.hasLaw_pi hX
  have hcoord (t : Σ j, Fin (k j)) : AEMeasurable (fun x ↦ f (x t)) (S.sampleLaw k) :=
    ((S.memLp_cond hf t.1).comp_measurePreserving (S.measurePreserving_draw k t)).aemeasurable
  have he : AEMeasurable (S.estimator f k) (S.sampleLaw k) := by
    apply Finset.aemeasurable_fun_sum
    intro j _
    exact aemeasurable_const.mul
      ((Finset.aemeasurable_fun_sum _ fun i _ ↦ hcoord ⟨j, i⟩).div_const _)
  rw [← S.variance_proportional hf hn hk, ← hjoint.map_eq,
    variance_map (hjoint.map_eq ▸ he) hjoint.aemeasurable]
  rfl

/-- The mean of `n` observations evaluated by the integrand. Under `Measure.pi (fun _ ↦ μ)`
this is ordinary i.i.d. Monte Carlo. -/
def plainMean (f : α → ℝ) (n : ℕ) (x : Fin n → α) : ℝ := (∑ i, f (x i)) / n

/-- Variance of the plain i.i.d. estimator sampled directly from the population law. -/
theorem variance_plainMean {f : α → ℝ} (hf : MemLp f 2 μ) {n : ℕ} (hn : 0 < n) :
    Var[plainMean f n; Measure.pi (fun _ : Fin n ↦ μ)] = Var[f; μ] / n := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let ν := fun _ : Fin n ↦ μ
  have h := variance_sample_mean (sigma2 := Var[f; μ]) (X := fun i (x : Fin n → α) ↦ f (x i))
    (fun i ↦ hf.comp_measurePreserving (measurePreserving_eval ν i))
    (iIndepFun_pi (μ := ν) fun _ ↦ hf.aemeasurable)
    (fun i ↦ (measurePreserving_eval ν i).variance_fun_comp hf.aemeasurable)
  change Var[fun x : Fin n → α ↦ (∑ i, f (x i)) / n; Measure.pi ν] = _
  simpa only [Fintype.card_fin] using h

/-- For the same number of draws, stratification cannot have larger variance than plain MC. -/
theorem variance_le_plainMean {f : α → ℝ} (hf : MemLp f 2 μ) {k : J → ℕ} {n : ℕ}
    (hn : 0 < n) (hk : ∀ j, (k j : ℝ) = n * S.weight j) :
    Var[S.estimator f k; S.sampleLaw k] ≤ Var[plainMean f n; Measure.pi (fun _ : Fin n ↦ μ)] := by
  rw [S.variance_proportional hf hn hk, variance_plainMean hf hn,
    S.variance_eq_within_add_between hf]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact le_add_of_nonneg_right <| Finset.sum_nonneg fun j _ ↦
    mul_nonneg (S.weight_pos j).le (sq_nonneg _)

/-- For an exact common budget, the two estimator variances are the corresponding cost-variance
products divided by the budget. Stratification is at least as efficient if and only if its
cost-variance product is no greater. Both sample sizes are natural numbers; neither is rounded. -/
theorem equal_budget {f : α → ℝ} (hf : MemLp f 2 μ) {k : J → ℕ} {ns np : ℕ}
    {C cs cp : ℝ} (hC : 0 < C) (hs : 0 < cs) (hp : 0 < cp)
    (hns : (ns : ℝ) * cs = C) (hnp : (np : ℝ) * cp = C)
    (hk : ∀ j, (k j : ℝ) = ns * S.weight j) :
    Var[S.estimator f k; S.sampleLaw k] = cs * S.withinVariance f / C ∧
    Var[plainMean f np; Measure.pi (fun _ : Fin np ↦ μ)] = cp * Var[f; μ] / C ∧
    (Var[S.estimator f k; S.sampleLaw k] ≤ Var[plainMean f np; Measure.pi (fun _ : Fin np ↦ μ)] ↔
      cs * S.withinVariance f ≤ cp * Var[f; μ]) := by
  have hs' : 0 < ns := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hns; linarith
  have hp' : 0 < np := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hnp; linarith
  have budget {m : ℕ} {c : ℝ} (hm : 0 < m) (hc : 0 < c) (h : (m : ℝ) * c = C) (v : ℝ) :
      v / m = c * v / C := by rw [← h]; field_simp
  rw [S.variance_proportional hf hs' hk, variance_plainMean hf hp', budget hs' hs hns,
    budget hp' hp hnp, div_le_div_iff_of_pos_right hC]
  exact ⟨rfl, rfl, Iff.rfl⟩

end Stratification
end MathlibExt.Probability
