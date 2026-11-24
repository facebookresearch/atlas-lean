/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.EmpiricalDistribution
public import MathlibExt.Probability.McDiarmid

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# A high-probability L1 bound for empirical frequencies

For `n` i.i.d. samples from a distribution `p` on a finite alphabet
of size `k`, the expected `L1` distance between the empirical
frequencies and `p` is at most `√(k / n)`, by `empFreq_l1_expectation`.
Changing one sample moves two empirical frequencies by `1 / n` each,
so the `L1` distance has sensitivity `2 / n`, and McDiarmid's
inequality (`mcdiarmid_one_sided_finite_iid_general`) gives the tail
bound `Pr[L1 - √(k / n) ≥ t] ≤ exp(-n t ^ 2 / 2)`. Both probabilities
use the suppliers' finite product-weight form.
-/

/-- The `PMF` weights sum to one. -/
private theorem mass_sum {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  have h1 := p.tsum_coe
  have h2 := ENNReal.tsum_toReal_eq (fun a => p.apply_ne_top a)
  rw [h1, ENNReal.toReal_one, tsum_fintype] at h2
  exact h2.symm

/-- The `L1` distance has sensitivity `2 / n` in each sample coordinate. -/
private theorem l1_sensitivity {α : Type*} [Fintype α] [DecidableEq α]
    (p : PMF α) {n : ℕ} (hn : 0 < n)
    (i : Fin n) (x y : Fin n → α)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    |(∑ a, |empFreq x a - (p a).toReal|) -
        (∑ a, |empFreq y a - (p a).toReal|)| ≤ 2 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcard : ∀ (z : Fin n → α) (a : α),
      (((Finset.univ.filter (fun j => z j = a)).card : ℕ) : ℝ)
        = ∑ j, (if z j = a then (1 : ℝ) else 0) := by
    intro z a
    exact (Finset.sum_boole (fun j => z j = a) Finset.univ).symm
  have hdiff : ∀ a, |empFreq x a - empFreq y a| ≤
      (∑ j, |(if x j = a then (1 : ℝ) else 0) -
        (if y j = a then (1 : ℝ) else 0)|) / (n : ℝ) := by
    intro a
    have h1 : empFreq x a - empFreq y a =
        ((∑ j, (if x j = a then (1 : ℝ) else 0)) -
          (∑ j, (if y j = a then (1 : ℝ) else 0))) / (n : ℝ) := by
      unfold empFreq
      rw [hcard x a, hcard y a, ← sub_div]
    rw [h1, abs_div, abs_of_nonneg hnR.le, ← Finset.sum_sub_distrib,
      div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _)
      (inv_nonneg.mpr hnR.le)
  have hzero : ∀ j : Fin n, j ≠ i →
      (∑ a, |(if x j = a then (1 : ℝ) else 0) -
        (if y j = a then (1 : ℝ) else 0)|) = 0 := by
    intro j hji
    have hxyj : x j = y j := hxy j hji
    rw [hxyj]
    simp
  have habs : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |s - t| ≤ s + t := by
    intro s t hs ht
    have h := abs_add_le s (-t)
    rw [abs_neg, abs_of_nonneg hs, abs_of_nonneg ht] at h
    rwa [sub_eq_add_neg]
  have htwo : ∀ j : Fin n,
      (∑ a, |(if x j = a then (1 : ℝ) else 0) -
        (if y j = a then (1 : ℝ) else 0)|) ≤ 2 := by
    intro j
    have e1 : (∑ a, (if x j = a then (1 : ℝ) else 0)) = 1 := by simp
    have e2 : (∑ a, (if y j = a then (1 : ℝ) else 0)) = 1 := by simp
    calc (∑ a, |(if x j = a then (1 : ℝ) else 0) -
            (if y j = a then (1 : ℝ) else 0)|)
        ≤ ∑ a, ((if x j = a then (1 : ℝ) else 0) +
            (if y j = a then (1 : ℝ) else 0)) := by
          apply Finset.sum_le_sum
          intro a _
          exact habs _ _ (by positivity) (by positivity)
      _ = 2 := by
          rw [Finset.sum_add_distrib, e1, e2]
          exact one_add_one_eq_two
  have hsingle : (∑ j, ∑ a, |(if x j = a then (1 : ℝ) else 0) -
        (if y j = a then (1 : ℝ) else 0)|)
      = ∑ a, |(if x i = a then (1 : ℝ) else 0) -
        (if y i = a then (1 : ℝ) else 0)| :=
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      (fun j _ hji => hzero j hji)
  have htriangle : |(∑ a, |empFreq x a - (p a).toReal|) -
      (∑ a, |empFreq y a - (p a).toReal|)|
      ≤ ∑ a, |empFreq x a - empFreq y a| := by
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_sum ?_)
    intro a _
    have h := abs_abs_sub_abs_le_abs_sub (empFreq x a - (p a).toReal)
      (empFreq y a - (p a).toReal)
    have heq : (empFreq x a - (p a).toReal) - (empFreq y a - (p a).toReal)
        = empFreq x a - empFreq y a := by ring
    rw [heq] at h
    exact h
  have hcount : (∑ a, |empFreq x a - empFreq y a|) ≤ 2 / (n : ℝ) := by
    calc (∑ a, |empFreq x a - empFreq y a|)
        ≤ ∑ a, ((∑ j, |(if x j = a then (1 : ℝ) else 0) -
            (if y j = a then (1 : ℝ) else 0)|) / (n : ℝ)) :=
          Finset.sum_le_sum (fun a _ => hdiff a)
      _ = (∑ a, ∑ j, |(if x j = a then (1 : ℝ) else 0) -
            (if y j = a then (1 : ℝ) else 0)|) / (n : ℝ) :=
          (Finset.sum_div _ _ _).symm
      _ = (∑ j, ∑ a, |(if x j = a then (1 : ℝ) else 0) -
            (if y j = a then (1 : ℝ) else 0)|) / (n : ℝ) := by
          rw [Finset.sum_comm]
      _ = (∑ a, |(if x i = a then (1 : ℝ) else 0) -
            (if y i = a then (1 : ℝ) else 0)|) / (n : ℝ) := by
          rw [hsingle]
      _ ≤ 2 / (n : ℝ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (htwo i)
            (inv_nonneg.mpr hnR.le)
  exact le_trans htriangle hcount

/-- One-sided deviation bound for the empirical `L1` distance above
its expectation bound `√(k / n)`. -/
theorem empFreq_l1_deviation {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (p : PMF α) {n : ℕ} (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    (∑ x ∈ Finset.univ.filter (fun x : Fin n → α =>
      decide (t ≤ (∑ a, |empFreq x a - (p a).toReal|) -
        Real.sqrt (Fintype.card α / n))), ∏ i, (p (x i)).toReal) ≤
    Real.exp (-(n : ℝ) * t ^ 2 / 2) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hsum : (∑ _i : Fin n, (2 / (n : ℝ)) ^ 2) = 4 / (n : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    ring
  have hc_pos : 0 < ∑ _i : Fin n, (2 / (n : ℝ)) ^ 2 := by
    rw [hsum]
    positivity
  have hmc : (∑ x ∈ Finset.univ.filter (fun x : Fin n → α =>
        decide (t ≤ (∑ a, |empFreq x a - (p a).toReal|) -
          (∑ x : Fin n → α, (∏ i, (p (x i)).toReal) *
            (∑ a, |empFreq x a - (p a).toReal|)))),
        ∏ i, (p (x i)).toReal) ≤
      Real.exp (-2 * t ^ 2 / (∑ _i : Fin n, (2 / (n : ℝ)) ^ 2)) :=
    MathlibExt.Probability.McDiarmid.mcdiarmid_one_sided_finite_iid_general
      (fun a => (p a).toReal) (fun a => ENNReal.toReal_nonneg) (mass_sum p)
      (fun x : Fin n → α => ∑ a, |empFreq x a - (p a).toReal|)
      (fun _ => 2 / (n : ℝ))
      (fun _ => show (0 : ℝ) ≤ 2 / (n : ℝ) from by positivity) hc_pos t ht
      (fun i x y hxy => l1_sensitivity p hn i x y hxy)
  have hμ := empFreq_l1_expectation p hn
  have hexp : -2 * t ^ 2 / (∑ _i : Fin n, (2 / (n : ℝ)) ^ 2)
      = -(n : ℝ) * t ^ 2 / 2 := by
    rw [hsum]
    field_simp
    ring
  rw [hexp] at hmc
  have hsub : Finset.univ.filter (fun x : Fin n → α =>
        decide (t ≤ (∑ a, |empFreq x a - (p a).toReal|) -
          Real.sqrt (Fintype.card α / n))) ⊆
      Finset.univ.filter (fun x : Fin n → α =>
        decide (t ≤ (∑ a, |empFreq x a - (p a).toReal|) -
          (∑ x : Fin n → α, (∏ i, (p (x i)).toReal) *
            (∑ a, |empFreq x a - (p a).toReal|)))) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq] at hx ⊢
    exact le_trans hx (by linarith [hμ])
  exact le_trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => Finset.prod_nonneg (fun i _ => ENNReal.toReal_nonneg)))
    hmc

/-- Confidence form: with product weight at most `δ`, the empirical
`L1` distance exceeds `√(k / n) + √(2 log (1 / δ) / n)`. -/
theorem empFreq_l1_high_probability {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (p : PMF α) {n : ℕ} (hn : 0 < n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∑ x ∈ Finset.univ.filter (fun x : Fin n → α =>
      decide (Real.sqrt ((Fintype.card α : ℝ) / n) +
        Real.sqrt (2 * Real.log (1 / δ) / n) ≤
          ∑ a, |empFreq x a - (p a).toReal|)), ∏ i, (p (x i)).toReal) ≤
    δ := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have h1δ : (1 : ℝ) < 1 / δ := by
    rw [lt_div_iff₀ hδ0]
    linarith
  have hlog : 0 < Real.log (1 / δ) := Real.log_pos h1δ
  have hT2 : (Real.sqrt (2 * Real.log (1 / δ) / (n : ℝ))) ^ 2
      = 2 * Real.log (1 / δ) / (n : ℝ) := by
    apply Real.sq_sqrt
    positivity
  have hT : 0 < Real.sqrt (2 * Real.log (1 / δ) / (n : ℝ)) :=
    Real.sqrt_pos.mpr (by positivity)
  have hexp : -(n : ℝ) * (Real.sqrt (2 * Real.log (1 / δ) / (n : ℝ))) ^ 2 / 2
      = Real.log δ := by
    rw [hT2]
    have hlogneg : Real.log (1 / δ) = -Real.log δ := by
      rw [one_div, Real.log_inv]
    rw [hlogneg]
    field_simp
  have h1 := empFreq_l1_deviation p hn _ hT
  rw [hexp, Real.exp_log hδ0] at h1
  have hfilter : Finset.univ.filter (fun x : Fin n → α =>
        decide (Real.sqrt ((Fintype.card α : ℝ) / n) +
          Real.sqrt (2 * Real.log (1 / δ) / n) ≤
            ∑ a, |empFreq x a - (p a).toReal|)) =
      Finset.univ.filter (fun x : Fin n → α =>
        decide (Real.sqrt (2 * Real.log (1 / δ) / (n : ℝ)) ≤
          (∑ a, |empFreq x a - (p a).toReal|) -
            Real.sqrt (Fintype.card α / n))) := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq]
    constructor <;> intro h <;> linarith
  rw [hfilter]
  exact h1

/-- Total-variation form: with product weight at most `δ`, half the
empirical `L1` distance exceeds half the confidence bound. -/
theorem empFreq_tv_high_probability {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (p : PMF α) {n : ℕ} (hn : 0 < n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∑ x ∈ Finset.univ.filter (fun x : Fin n → α =>
      decide ((Real.sqrt ((Fintype.card α : ℝ) / n) +
        Real.sqrt (2 * Real.log (1 / δ) / n)) / 2 ≤
          (∑ a, |empFreq x a - (p a).toReal|) / 2)),
        ∏ i, (p (x i)).toReal) ≤
    δ := by
  have h2 := empFreq_l1_high_probability p hn δ hδ0 hδ1
  have hfilter : Finset.univ.filter (fun x : Fin n → α =>
        decide ((Real.sqrt ((Fintype.card α : ℝ) / n) +
          Real.sqrt (2 * Real.log (1 / δ) / n)) / 2 ≤
            (∑ a, |empFreq x a - (p a).toReal|) / 2)) =
      Finset.univ.filter (fun x : Fin n → α =>
        decide (Real.sqrt ((Fintype.card α : ℝ) / n) +
          Real.sqrt (2 * Real.log (1 / δ) / n) ≤
            ∑ a, |empFreq x a - (p a).toReal|)) := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq]
    constructor <;> intro h <;> linarith
  rw [hfilter]
  exact h2
