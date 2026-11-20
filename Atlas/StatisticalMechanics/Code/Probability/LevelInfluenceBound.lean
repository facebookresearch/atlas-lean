/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Code.Probability.DegreeTruncation

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]







theorem lib_optimal_exponent {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (2 : ℝ) / (2 - u) - 1 = u / (2 - u) := by
  have h2u : (0 : ℝ) < 2 - u := by linarith
  rw [div_sub_one (ne_of_gt h2u)]; congr 1; ring















theorem lib_level1_mass_le [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1),
        (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ 4 * p * (1 - p)
        * (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set σ2 := (ptn_sigma p) ^ 2 with hσ2def
  have hσ2 : σ2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have hσ2pos : 0 < σ2 := by rw [hσ2]; nlinarith
  have hprob := OSSS.bernoulliWeight_isProbWeight (E := ι) hp0.le hp1.le
  
  set q' : ℝ := 2 - u with hq'
  have hq1 : (1 : ℝ) ≤ q' := by rw [hq']; linarith
  have hq2 : q' ≤ 2 := by rw [hq']; linarith
  have h2q' : (2 : ℝ) / q' - 1 = u / (2 - u) := by rw [hq']; exact lib_optimal_exponent hu0 hu1
  
  set ρ : ℝ := Real.sqrt ((q' - 1) * 4 * p * (1 - p)) with hρ
  have hsnn : (0 : ℝ) ≤ (q' - 1) * 4 * p * (1 - p) := by rw [hq']; nlinarith
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρsq : ρ ^ 2 = (q' - 1) * 4 * p * (1 - p) := by rw [hρ, Real.sq_sqrt hsnn]
  have hρ1 : ρ ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm, hρ]
    apply Real.sqrt_le_sqrt
    rw [hq']; nlinarith [sq_nonneg (1 - 2 * p)]
  have hθ1 : (1 : ℝ) ≤ 2 / q' := by rw [le_div_iff₀ (by linarith : (0:ℝ) < q')]; linarith
  
  have hper : ∀ e : ι,
      (ptn_coeff p f {e}) ^ 2 ≤ σ2 * (δ ^ (u / (2 - u)) * OSSS.infl (OSSS.bernoulliWeight p) f e) := by
    intro e
    have hpc := ptn_perCoord_hc hp0 hp1 hρ0 hρ1 hq1 hq2 hρsq φ e
    
    have hmem : ({e} : Finset ι) ∈ univ.filter (fun S : Finset ι => e ∈ S) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, Finset.mem_singleton_self e⟩
    have hsingle_term : (ρ ^ (({e} : Finset ι).erase e).card) ^ 2 * (ptn_coeff p f {e} / ptn_sigma p) ^ 2
        = (ptn_coeff p f {e} / ptn_sigma p) ^ 2 := by
      rw [Finset.erase_singleton, Finset.card_empty, pow_zero, one_pow, one_mul]
    
    have hge : (ptn_coeff p f {e} / ptn_sigma p) ^ 2
        ≤ ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
            (ρ ^ (S.erase e).card) ^ 2 * (ptn_coeff p f S / ptn_sigma p) ^ 2 := by
      rw [← hsingle_term]
      apply Finset.single_le_sum (f := fun S => (ρ ^ (S.erase e).card) ^ 2 * (ptn_coeff p f S / ptn_sigma p) ^ 2)
        (fun S _ => by positivity) hmem
    have hIe : (ptn_coeff p f {e} / ptn_sigma p) ^ 2 ≤ (OSSS.infl (OSSS.bernoulliWeight p) f e) ^ (2 / q') :=
      le_trans hge hpc
    
    have hcap : (OSSS.infl (OSSS.bernoulliWeight p) f e) ^ (2 / q')
        ≤ δ ^ (2 / q' - 1) * OSSS.infl (OSSS.bernoulliWeight p) f e :=
      bph_cap_term _ _ _ (kkl_infl_nonneg hprob f e) (kkl_infl_le_maxInfl _ f e) hθ1
    rw [h2q'] at hcap
    
    have hσne : (ptn_sigma p) ^ 2 ≠ 0 := by rw [← hσ2def]; exact ne_of_gt hσ2pos
    have hcoeff : σ2 * (ptn_coeff p f {e} / ptn_sigma p) ^ 2 = (ptn_coeff p f {e}) ^ 2 := by
      rw [div_pow, hσ2def, mul_div_assoc', mul_comm, mul_div_assoc,
        div_self hσne, mul_one]
    rw [← hcoeff]
    apply mul_le_mul_of_nonneg_left (le_trans hIe hcap) hσ2pos.le
  
  
  have hreindex : (∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), (ptn_coeff p f S) ^ 2)
      = ∑ e : ι, (ptn_coeff p f {e}) ^ 2 := by
    have hset : univ.filter (fun S : Finset ι => S.card = 1)
        = (Finset.univ : Finset ι).map ⟨fun e => ({e} : Finset ι), fun a b h => by simpa using h⟩ := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · intro hS; obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hS; exact ⟨a, ha.symm⟩
      · rintro ⟨e, rfl⟩; exact Finset.card_singleton e
    rw [hset, Finset.sum_map]
    rfl
  rw [hreindex]
  
  calc (4 : ℝ) * ∑ e : ι, (ptn_coeff p f {e}) ^ 2
      ≤ 4 * ∑ e : ι, σ2 * (δ ^ (u / (2 - u)) * OSSS.infl (OSSS.bernoulliWeight p) f e) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum (fun e _ => hper e)
    _ = 4 * σ2 * δ ^ (u / (2 - u)) * (∑ e : ι, OSSS.infl (OSSS.bernoulliWeight p) f e) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _; ring
    _ = 4 * p * (1 - p) * δ ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) f := by
        rw [hσ2, totalInfl]; ring













theorem lib_capped_optimal_weight [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    4 * ∑ S : Finset ι, (S.card : ℝ)
        * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * p * (1 - p)
        * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set σ2 := (ptn_sigma p) ^ 2 with hσ2def
  have hσ2 : σ2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have hσ2pos : 0 < σ2 := by rw [hσ2]; nlinarith
  
  set q' : ℝ := 2 - u with hq'
  have hq1 : (1 : ℝ) ≤ q' := by rw [hq']; linarith
  have hq2 : q' ≤ 2 := by rw [hq']; linarith
  have h2q' : (2 : ℝ) / q' - 1 = u / (2 - u) := by rw [hq']; exact lib_optimal_exponent hu0 hu1
  set ρ : ℝ := Real.sqrt ((q' - 1) * 4 * p * (1 - p)) with hρ
  have hsnn : (0 : ℝ) ≤ (q' - 1) * 4 * p * (1 - p) := by rw [hq']; nlinarith
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρsq : ρ ^ 2 = (q' - 1) * 4 * p * (1 - p) := by rw [hρ, Real.sq_sqrt hsnn]
  have hρ1 : ρ ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm, hρ]
    apply Real.sqrt_le_sqrt; rw [hq']; nlinarith [sq_nonneg (1 - 2 * p)]
  have hcap := ptn_capped_hc hp0 hp1 hρ0 hρ1 hq1 hq2 hρsq φ
  rw [h2q'] at hcap
  
  have hρsq2 : ρ ^ 2 = (1 - u) * (4 * p * (1 - p)) := by rw [hρsq, hq']; ring
  have hweight : ∀ S : Finset ι, (ρ ^ (S.card - 1)) ^ 2 = ((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1) := by
    intro S; rw [← pow_mul, mul_comm (S.card - 1) 2, pow_mul, hρsq2]
  
  
  have hkey : (4 : ℝ) * ∑ S : Finset ι, (S.card : ℝ)
        * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1) * (ptn_coeff p f S) ^ 2)
      = 4 * σ2 * ((1 / σ2) * ∑ S : Finset ι, (S.card : ℝ)
          * ((ρ ^ (S.card - 1)) ^ 2 * (ptn_coeff p f S) ^ 2)) := by
    rw [show (4 : ℝ) * σ2 * ((1 / σ2) * (∑ S : Finset ι, (S.card : ℝ)
          * ((ρ ^ (S.card - 1)) ^ 2 * (ptn_coeff p f S) ^ 2)))
        = (4 * (σ2 * (1 / σ2))) * (∑ S : Finset ι, (S.card : ℝ)
          * ((ρ ^ (S.card - 1)) ^ 2 * (ptn_coeff p f S) ^ 2)) from by ring]
    rw [mul_one_div, div_self (ne_of_gt hσ2pos), mul_one]
    congr 1
    apply Finset.sum_congr rfl; intro S _; rw [hweight]
  rw [hkey]
  
  have h4σ : (0 : ℝ) ≤ 4 * σ2 := by positivity
  calc (4 : ℝ) * σ2 * ((1 / σ2) * ∑ S : Finset ι, (S.card : ℝ)
          * ((ρ ^ (S.card - 1)) ^ 2 * (ptn_coeff p f S) ^ 2))
      ≤ 4 * σ2 * ((maxInfl (OSSS.bernoulliWeight p) f) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) f) :=
        mul_le_mul_of_nonneg_left hcap h4σ
    _ = 4 * p * (1 - p) * ((maxInfl (OSSS.bernoulliWeight p) f) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) f) := by
        rw [hσ2]; ring
















theorem lib_residue_iff_levelGe2 {p : ℝ}
    (φ : ConfigSpace ι → Bool) {u : ℝ}
    {k : ℕ} (hk : 1 ≤ k) {B : ℝ} :
    (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 1 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ B)
      ↔ (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (S.card : ℝ) * (1 - u) ^ (S.card - 1)
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
        ≤ B - 4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1),
            (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
  set c := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hc
  
  have hsplit : (∑ S ∈ univ.filter (fun S : Finset ι => 1 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S)
      = (∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), c S)
        + ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
            (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S := by
    rw [← Finset.sum_filter_add_sum_filter_not (univ.filter (fun S : Finset ι => 1 ≤ S.card ∧ S.card ≤ k))
        (fun S => S.card = 1)
        (fun S => (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S)]
    congr 1
    · 
      rw [show (univ.filter (fun S : Finset ι => 1 ≤ S.card ∧ S.card ≤ k)).filter (fun S => S.card = 1)
          = univ.filter (fun S : Finset ι => S.card = 1) from ?_]
      · apply Finset.sum_congr rfl; intro S hS
        rw [Finset.mem_filter] at hS
        rw [hS.2, Nat.cast_one, show (1 : ℕ) - 1 = 0 from rfl, pow_zero, one_mul, one_mul]
      · ext S
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, h⟩; exact h
        · intro h; exact ⟨⟨by omega, by omega⟩, h⟩
    · 
      rw [show (univ.filter (fun S : Finset ι => 1 ≤ S.card ∧ S.card ≤ k)).filter (fun S => ¬ S.card = 1)
          = univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k) from ?_]
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨h1, h2⟩, hne⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, by omega⟩
  rw [hsplit, mul_add]
  constructor
  · intro h; linarith
  · intro h; linarith





















def lib_levelGe2Residue (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) < Real.exp (-1) →
      ∀ u : ℝ, 0 < u → u < 1 →
        (u < 1 - 4 * p * (1 - p) ∨
          (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
              ^ (u / (2 - u) - (2 / (1 + (1 - u) / (4 * p * (1 - p))) - 1))
            < 4 * (ptn_sigma p) ^ 2) →
        ∃ k : ℕ, 1 ≤ k ∧
          4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
              (S.card : ℝ) * (1 - u) ^ (S.card - 1)
                * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
            ≤ ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
                ^ (u / (2 - u))
              - 4 * p * (1 - p) * (1 - u) ^ k
              - 4 * p * (1 - p)
                * (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
                  ^ (u / (2 - u)))
              * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)










theorem lib_levelGe2_discharges {q : ℝ} (H : lib_levelGe2Residue q) :
    dtr_lowDegreeResidue q := by
  intro p hp hp1 E _ _ _ φ hδ u hu0 hu1 hlow
  have hp0 : 0 < p := by have := hp.1; linarith
  
  obtain ⟨k, hk1, hk⟩ := H p hp hp1 φ hδ u hu0 hu1 hlow
  set f := fun ω : ConfigSpace E => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδdef
  set T := totalInfl (OSSS.bernoulliWeight p) f with hTdef
  
  have hlvl1 : 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1), (ptn_coeff p f S) ^ 2
      ≤ 4 * p * (1 - p) * δ ^ (u / (2 - u)) * T := lib_level1_mass_le hp0 hp1 φ hu0 hu1
  
  set B : ℝ := (δ ^ (u / (2 - u)) - 4 * p * (1 - p) * (1 - u) ^ k) * T with hB
  
  have hrhs : ((δ ^ (u / (2 - u)) - 4 * p * (1 - p) * (1 - u) ^ k
        - 4 * p * (1 - p) * δ ^ (u / (2 - u))) * T)
      = B - 4 * p * (1 - p) * δ ^ (u / (2 - u)) * T := by rw [hB]; ring
  rw [hrhs] at hk
  
  have hk' : 4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
      (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p f S) ^ 2
      ≤ B - 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1), (ptn_coeff p f S) ^ 2 := by
    refine le_trans hk ?_
    linarith [hlvl1]
  
  have hfinal := (lib_residue_iff_levelGe2 φ hk1 (B := B)).mpr hk'
  exact ⟨k, hfinal⟩









theorem lib_levelGe2_budget_pos {p δ u : ℝ} (hphalf : 1 / 2 < p) (hp1 : p < 1) (hu0 : 0 < u)
    (_hu1 : u < 1) (hδ0 : 0 < δ ^ (u / (2 - u))) :
    ∃ k : ℕ, 1 ≤ k ∧ 0 ≤ δ ^ (u / (2 - u)) - 4 * p * (1 - p) * (1 - u) ^ k
        - 4 * p * (1 - p) * δ ^ (u / (2 - u)) := by
  have hp0 : 0 < p := by linarith
  have hs0 : 0 < 4 * p * (1 - p) := by nlinarith
  have hs1 : 4 * p * (1 - p) < 1 := by nlinarith [sq_nonneg (1 - 2 * p), mul_pos (by linarith : (0:ℝ) < 2*p - 1) (by linarith : (0:ℝ) < 2*p - 1)]
  have h1u : (1 : ℝ) - u < 1 := by linarith
  
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (x := ((1 - 4 * p * (1 - p)) * δ ^ (u / (2 - u))) / (4 * p * (1 - p)))
    (by positivity) h1u
  refine ⟨k + 1, by omega, ?_⟩
  rw [lt_div_iff₀ hs0] at hk
  have hmono : (1 - u) ^ (k + 1) ≤ (1 - u) ^ k :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
  nlinarith [hk, hmono, hs0]







theorem lib_level1_mass_nonneg [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 ≤ 4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1),
        (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ∧ 4 * ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1),
        (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
        ≤ 4 * p * (1 - p)
          * (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  refine ⟨?_, lib_level1_mass_le hp0 hp1 φ hu0 hu1⟩
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun S _ => sq_nonneg _)

end StatMech.Probability
