/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Code.Probability.TwoPointHCqGt2

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]











theorem dtr_full_weight_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool) :
    4 * ∑ S : Finset ι, (S.card : ℝ)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      = 4 * p * (1 - p) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hσ2 : (ptn_sigma p) ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have hσ2pos : 0 < (ptn_sigma p) ^ 2 := pow_pos (ptn_sigma_pos hp0 hp1) 2
  rw [ptn_totalInfl_eq_fourierWeight hp0 hp1]
  rw [hσ2]
  have hppos : 0 < p * (1 - p) := by nlinarith
  set W := ∑ S : Finset ι, (S.card : ℝ)
      * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hW
  rw [show (4 : ℝ) * p * (1 - p) * (1 / (p * (1 - p)) * W)
      = (4 * (p * (1 - p)) * (1 / (p * (1 - p)))) * W by ring]
  rw [mul_one_div, mul_div_assoc, div_self (ne_of_gt hppos), mul_one]





theorem dtr_pow_mono_exp {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) {k m : ℕ} (hkm : k ≤ m) :
    x ^ m ≤ x ^ k :=
  pow_le_pow_of_le_one h0 h1 hkm








theorem dtr_high_part_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (k : ℕ) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (1 - u) ^ k * (4 * p * (1 - p)
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  set c := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hc
  have h1u0 : (0 : ℝ) ≤ 1 - u := by linarith
  have h1u1 : (1 : ℝ) - u ≤ 1 := by linarith
  
  have hterm : ∀ S ∈ univ.filter (fun S : Finset ι => k < S.card),
      4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S
        ≤ (1 - u) ^ k * (4 * (S.card : ℝ) * c S) := by
    intro S hS
    rw [Finset.mem_filter] at hS
    have hkS : k ≤ S.card - 1 := by omega
    have hpow : (1 - u) ^ (S.card - 1) ≤ (1 - u) ^ k := dtr_pow_mono_exp h1u0 h1u1 hkS
    have hcoef : (0 : ℝ) ≤ 4 * (S.card : ℝ) * c S := by positivity
    nlinarith [hpow, hcoef, Real.rpow_natCast (1 - u) k]
  
  rw [Finset.mul_sum]
  calc (∑ S ∈ univ.filter (fun S : Finset ι => k < S.card),
          4 * ((S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S))
      = ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card),
          4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S := by
        apply Finset.sum_congr rfl; intro S _; ring
    _ ≤ ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card), (1 - u) ^ k * (4 * (S.card : ℝ) * c S) :=
        Finset.sum_le_sum hterm
    _ = (1 - u) ^ k * ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card), 4 * (S.card : ℝ) * c S := by
        rw [Finset.mul_sum]
    _ ≤ (1 - u) ^ k * ∑ S : Finset ι, 4 * (S.card : ℝ) * c S := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro S _ _; positivity
    _ = (1 - u) ^ k * (4 * ∑ S : Finset ι, (S.card : ℝ) * c S) := by
        congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro S _; ring
    _ = (1 - u) ^ k * (4 * p * (1 - p)
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
        rw [dtr_full_weight_eq hp0 hp1 φ]












theorem dtr_trunc_split {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (k : ℕ) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 1 ≤ S.card ∧ S.card ≤ k),
            (S.card : ℝ) * (1 - u) ^ (S.card - 1)
              * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        + (1 - u) ^ k * (4 * p * (1 - p)
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  set c := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hc
  set g := fun S : Finset ι => 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S with hg
  have hgnn : ∀ S, 0 ≤ g S := by
    intro S; rw [hg]; have h1u0 : (0 : ℝ) ≤ 1 - u := by linarith
    positivity
  
  have hsplit : (∑ S : Finset ι, g S)
      = (∑ S ∈ univ.filter (fun S : Finset ι => S.card ≤ k), g S)
        + ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card), g S := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun S : Finset ι => S.card ≤ k) g]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext S; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  rw [hsplit]
  apply add_le_add
  · 
    
    apply le_of_eq
    have hRHS : (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 1 ≤ S.card ∧ S.card ≤ k),
          (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S)
        = ∑ S ∈ univ.filter (fun S : Finset ι => 1 ≤ S.card ∧ S.card ≤ k), g S := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro S _; rw [hg]; ring
    rw [hRHS]
    symm
    apply Finset.sum_subset
    · intro S hS
      rw [Finset.mem_filter] at hS ⊢
      exact ⟨hS.1, hS.2.2⟩
    · intro S hS hSnot
      rw [Finset.mem_filter] at hS hSnot
      have hc0 : S.card = 0 := by
        by_contra h
        exact hSnot ⟨Finset.mem_univ S, Nat.one_le_iff_ne_zero.mpr h, hS.2⟩
      show 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S = 0
      rw [hc0]; simp
  · 
    have hconv : (∑ S ∈ univ.filter (fun S : Finset ι => k < S.card), g S)
        = 4 * ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card),
            (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro S _; rw [hg]; ring
    rw [hconv]
    exact dtr_high_part_le hp0 hp1 φ hu0 hu1 k




private noncomputable def dtr_qstar (p u : ℝ) : ℝ := 1 + (1 - u) / (4 * p * (1 - p))

















def dtr_lowDegreeResidue (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) < Real.exp (-1) →
      ∀ u : ℝ, 0 < u → u < 1 →
        (u < 1 - 4 * p * (1 - p) ∨
          (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
              ^ (u / (2 - u) - (2 / dtr_qstar p u - 1))
            < 4 * (ptn_sigma p) ^ 2) →
        ∃ k : ℕ,
          4 * ∑ S ∈ univ.filter (fun S : Finset E => 1 ≤ S.card ∧ S.card ≤ k),
              (S.card : ℝ) * (1 - u) ^ (S.card - 1)
                * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
            ≤ ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
                ^ (u / (2 - u))
              - 4 * p * (1 - p) * (1 - u) ^ k)
              * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)






theorem dtr_lowDegree_of_residue {q : ℝ} (H : dtr_lowDegreeResidue q) :
    hcq_lowRangeResidue q := by
  intro p hp hp1 E _ _ _ φ hδ u hu0 hu1 hlow
  have hp0 : 0 < p := by have := hp.1; linarith
  
  have hlow' : u < 1 - 4 * p * (1 - p) ∨
      (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u) - (2 / dtr_qstar p u - 1))
        < 4 * (ptn_sigma p) ^ 2 := by
    rcases hlow with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [dtr_qstar]; exact h)
  obtain ⟨k, hk⟩ := H p hp hp1 φ hδ u hu0 hu1 hlow'
  
  have hsplit := dtr_trunc_split hp0 hp1 φ hu0 hu1 k
  set T := totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hT
  set δ := maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hδdef
  calc (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (4 * ∑ S ∈ univ.filter (fun S : Finset E => 1 ≤ S.card ∧ S.card ≤ k),
            (S.card : ℝ) * (1 - u) ^ (S.card - 1)
              * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          + (1 - u) ^ k * (4 * p * (1 - p) * T) := hsplit
    _ ≤ (δ ^ (u / (2 - u)) - 4 * p * (1 - p) * (1 - u) ^ k) * T
          + (1 - u) ^ k * (4 * p * (1 - p) * T) := by linarith [hk]
    _ = δ ^ (u / (2 - u)) * T := by ring




theorem dtr_smallDelta_of_residue {q : ℝ} (H : dtr_lowDegreeResidue q) :
    cvg_smallDeltaResidue q :=
  hcq_smallDelta_of_lowRange (dtr_lowDegree_of_residue H)



theorem dtr_martingaleHC_of_residue {q : ℝ} (H : dtr_lowDegreeResidue q) :
    mxd_martingaleHC_statement q :=
  cvg_martingaleHC_of_smallDelta (dtr_smallDelta_of_residue H)









theorem dtr_budget_pos {p δ u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 < u) (_hu1 : u < 1)
    (hδ0 : 0 < δ ^ (u / (2 - u))) :
    ∃ k : ℕ, 0 ≤ δ ^ (u / (2 - u)) - 4 * p * (1 - p) * (1 - u) ^ k := by
  have hs0 : 0 < 4 * p * (1 - p) := by nlinarith
  have h1u : (1 : ℝ) - u < 1 := by linarith
  
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (x := δ ^ (u / (2 - u)) / (4 * p * (1 - p)))
    (by positivity) h1u
  refine ⟨k, ?_⟩
  rw [lt_div_iff₀ hs0] at hk
  nlinarith [hk]





theorem dtr_residue_c0 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    (hδ0 : 0 < (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
        ^ (u / (2 - u))) :
    ∃ k : ℕ, (0 : ℝ)
      ≤ ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
          - 4 * p * (1 - p) * (1 - u) ^ k)
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  obtain ⟨k, hk⟩ := dtr_budget_pos hp0 hp1 hu0 hu1 hδ0
  refine ⟨k, ?_⟩
  apply mul_nonneg hk
  exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _










theorem dtr_high_part_proved {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (k : ℕ) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => k < S.card),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (1 - u) ^ k * (4 * p * (1 - p)
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :=
  dtr_high_part_le hp0 hp1 φ hu0 hu1 k

end StatMech.Probability
