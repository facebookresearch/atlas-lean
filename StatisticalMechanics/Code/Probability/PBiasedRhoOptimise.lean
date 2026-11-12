/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Code.Probability.RhoOptimiseEngine
import Code.Probability.PBiasedTensorize

open scoped BigOperators
open Finset
open Real Filter Topology
open StatMech StatMech.OSSS

set_option linter.style.longLine false

namespace StatMech.Probability
















def pro_PBiasedMaster (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 →
    ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool),
    ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
          * (4 * (ptn_sigma p) ^ 2
              * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))



theorem pro_degreeWeight_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] (φ : ConfigSpace E → Bool) :
    (∑ S : Finset E, 4 * (S.card : ℝ)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      = 4 * (ptn_sigma p) ^ 2
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hσ2 : (0:ℝ) < (ptn_sigma p) ^ 2 := by
    have := ptn_sigma_pos hp0 hp1; positivity
  rw [ptn_totalInfl_eq_fourierWeight hp0 hp1 φ]
  
  rw [show (4 * (ptn_sigma p) ^ 2 * ((1 / (ptn_sigma p) ^ 2)
        * ∑ S : Finset E, (S.card : ℝ)
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2))
      = 4 * (((ptn_sigma p) ^ 2 * (1 / (ptn_sigma p) ^ 2))
          * ∑ S : Finset E, (S.card : ℝ)
              * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) from by ring]
  rw [mul_one_div_cancel (ne_of_gt hσ2), one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro S _; ring










theorem pro_rhoOptimise_of_master {q : ℝ} (H : pro_PBiasedMaster q) :
    ptn_RhoOptimise q := by
  intro p hp hp1 E _ _ _ φ _Hcap
  have hp0 : 0 < p := by have := hp.1; linarith
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set c : Finset E → ℝ := fun S => (ptn_coeff p f S) ^ 2 with hc
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  have hcnn : ∀ S : Finset E, 0 ≤ c S := fun S => by rw [hc]; positivity
  have hδnn : 0 ≤ δ := by
    rw [hδ, hf]; exact kkl_maxInfl_nonneg
      (OSSS.bernoulliWeight_isProbWeight (E := E) hp0.le hp1.le) _
  have hTnn : 0 ≤ T := by
    rw [hT, hf]; exact kkl_totalInfl_nonneg
      (OSSS.bernoulliWeight_isProbWeight (E := E) hp0.le hp1.le) _
  
  have hWeq : (∑ S : Finset E, 4 * (S.card : ℝ) * c S) = 4 * (ptn_sigma p) ^ 2 * T := by
    rw [show (∑ S : Finset E, 4 * (S.card : ℝ) * c S)
          = ∑ S : Finset E, 4 * (S.card : ℝ) * (ptn_coeff p f S) ^ 2 from by
        apply Finset.sum_congr rfl; intro S _; rw [hc]]
    rw [hT, hf]; exact pro_degreeWeight_eq hp0 hp1 φ
  
  have Hmaster : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S)
        ≤ δ ^ (u / (2 - u)) * (∑ S : Finset E, 4 * (S.card : ℝ) * c S) := by
    intro u hu0 hu1
    have h := H p hp hp1 φ u hu0 hu1
    rw [hWeq]
    calc (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S)
        = (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
            * (ptn_coeff p f S) ^ 2) := by
          apply Finset.sum_congr rfl; intro S _; rw [hc]
      _ ≤ δ ^ (u / (2 - u)) * (4 * (ptn_sigma p) ^ 2 * T) := by rw [hδ, hT, hf] at *; exact h
  
  have hgain := roe_logGain_four (d := fun S : Finset E => S.card) hcnn hδnn Hmaster
  rw [hWeq] at hgain
  
  
  have hVar : (∑ S ∈ univ.filter (fun S : Finset E => S.card ≠ 0), c S)
      = OSSS.var (OSSS.bernoulliWeight p) f := by
    rw [hc, hf]
    rw [ptn_var_eq_fourierWeight hp0 hp1]
    apply Finset.sum_congr ?_ (fun S _ => rfl)
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    rw [Finset.card_ne_zero, Finset.nonempty_iff_ne_empty]
  rw [hVar] at hgain
  
  have hσ2le : 4 * (ptn_sigma p) ^ 2 ≤ 1 := by
    rw [ptn_sigma_sq hp0 hp1]; nlinarith [sq_nonneg (1 - 2 * p)]
  have hfin : 4 * (ptn_sigma p) ^ 2 * T ≤ T := by nlinarith [hTnn, hσ2le]
  
  linarith [hgain, hfin]











theorem pro_master_lhs_zero_of_totalInfl_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] (φ : ConfigSpace E → Bool)
    (hT : totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0)
    (u : ℝ) :
    (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) = 0 := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  have hσ2 : (0:ℝ) < (ptn_sigma p) ^ 2 := by have := ptn_sigma_pos hp0 hp1; positivity
  
  have hsum0 : (∑ S : Finset E, (S.card : ℝ) * (ptn_coeff p f S) ^ 2) = 0 := by
    have heq : (0:ℝ) = (1 / (ptn_sigma p) ^ 2)
        * ∑ S : Finset E, (S.card : ℝ) * (ptn_coeff p f S) ^ 2 := by
      rw [← ptn_totalInfl_eq_fourierWeight hp0 hp1 φ]; exact hT.symm
    rcases mul_eq_zero.mp heq.symm with h | h
    · exact absurd h (by positivity)
    · exact h
  
  have hterm0 : ∀ S : Finset E, (S.card : ℝ) * (ptn_coeff p f S) ^ 2 = 0 := by
    intro S
    have hnn : ∀ S' : Finset E, S' ∈ (Finset.univ : Finset (Finset E)) →
        0 ≤ (S'.card : ℝ) * (ptn_coeff p f S') ^ 2 := fun S' _ => by positivity
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 S (Finset.mem_univ S)
  
  apply Finset.sum_eq_zero
  intro S _
  rcases Nat.eq_zero_or_pos S.card with hc0 | hcpos
  · rw [hc0]; simp
  · have hcS : (ptn_coeff p f S) ^ 2 = 0 := by
      have hts := hterm0 S
      have hcard : (S.card : ℝ) ≠ 0 := by
        have : (0:ℕ) < S.card := hcpos
        exact_mod_cast this.ne'
      rcases mul_eq_zero.mp hts with h | h
      · exact absurd h hcard
      · exact h
    rw [hcS]; ring





theorem pro_master_holds_of_totalInfl_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    (hT : totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0)
    (u : ℝ) :
    (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * (4 * (ptn_sigma p) ^ 2
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  rw [pro_master_lhs_zero_of_totalInfl_zero hp0 hp1 φ hT u, hT]
  simp

end StatMech.Probability
