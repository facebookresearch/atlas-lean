/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Code.Probability.BKKKLLevel2Close

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]












theorem fs_lever {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (m : ℕ) :
    (m : ℝ) * x ^ (m - 1) * (y - x) ≤ y ^ m - x ^ m := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hfact : y ^ m - x ^ m = (∑ i ∈ Finset.range m, y ^ i * x ^ (m - 1 - i)) * (y - x) :=
    (geom_sum₂_mul y x m).symm
  rw [hfact]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · apply mul_le_mul_of_nonneg_right _ (by linarith)
    calc (m : ℝ) * x ^ (m - 1) = ∑ _i ∈ Finset.range m, x ^ (m - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range m, y ^ i * x ^ (m - 1 - i) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_range] at hi
          have hxi : x ^ i ≤ y ^ i := pow_le_pow_left₀ hx hxy i
          have hsplit : x ^ (m - 1) = x ^ i * x ^ (m - 1 - i) := by rw [← pow_add]; congr 1; omega
          rw [hsplit]
          exact mul_le_mul_of_nonneg_right hxi (by positivity)








theorem fs_degree_to_undegree {u u' : ℝ} (hu1 : u < 1) (hlt : u' < u) (m : ℕ) :
    (m : ℝ) * (1 - u) ^ (m - 1) ≤ (1 - u') ^ m / (u - u') := by
  have hx : (0 : ℝ) ≤ 1 - u := by linarith
  have hxy : (1 : ℝ) - u ≤ 1 - u' := by linarith
  have hdpos : 0 < u - u' := by linarith
  have hlever := fs_lever hx hxy m
  have hdiff : (1 - u') - (1 - u) = u - u' := by ring
  rw [hdiff] at hlever
  rw [le_div_iff₀ hdpos]
  nlinarith [hlever, pow_nonneg hx m]

















theorem bkt2f_targetWeight_levelGe2 [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u' : ℝ} (hu'0 : 0 < u') (hu'1 : u' < 1)
    (hcap : 1 - u' ≤ 4 * p * (1 - p)) (k : ℕ) :
    ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k), (1 - u') ^ S.card
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (ptn_qnorm p (1 + (1 - u') / (4 * p * (1 - p)))
          (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 := by
  set s := 4 * p * (1 - p) with hs
  have hs0 : 0 < s := by rw [hs]; nlinarith
  set q := 1 + (1 - u') / s with hq
  have hu1' : (0 : ℝ) ≤ 1 - u' := by linarith
  set ρ := Real.sqrt (1 - u') with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p) := by
    rw [hρ, Real.sq_sqrt hu1', hq]; field_simp; rw [hs]; ring
  have hq1 : 1 ≤ q := by rw [hq]; have : 0 ≤ (1 - u') / s := div_nonneg hu1' hs0.le; linarith
  have hq2 : q ≤ 2 := by
    rw [hq]; have : (1 - u') / s ≤ 1 := by rw [div_le_one hs0]; rw [hs]; linarith [hcap]
    linarith
  have hldw := ptn_lowDegreeWeight hp0 hp1 hρ0 hρ1 hq1 hq2 hρsq
    (fun ω => if φ ω then (1 : ℝ) else 0)
  have hpow : ∀ S : Finset ι, (ρ ^ S.card) ^ 2 = (1 - u') ^ S.card := by
    intro S; rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hu1']
  calc ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k), (1 - u') ^ S.card
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ ∑ S : Finset ι, (1 - u') ^ S.card
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro S _ _; positivity
    _ = ∑ S : Finset ι, (ρ ^ S.card) ^ 2
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
        apply Finset.sum_congr rfl; intro S _; rw [hpow]
    _ ≤ (ptn_qnorm p q (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 := hldw











theorem bkt2f_degreeWeight_le_undegree {u u' : ℝ} (hu1 : u < 1) (hlt : u' < u)
    (φ : ConfigSpace ι → Bool) {p : ℝ} (k : ℕ) :
    ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (1 / (u - u')) * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (1 - u') ^ S.card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  have hdpos : 0 < u - u' := by linarith
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  have hlever := fs_degree_to_undegree hu1 hlt S.card
  calc (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ ((1 - u') ^ S.card / (u - u'))
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 :=
        mul_le_mul_of_nonneg_right hlever (by positivity)
    _ = 1 / (u - u')
          * ((1 - u') ^ S.card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
        rw [div_mul_eq_mul_div, one_div]; ring
















theorem bkt2f_FS_highDegree [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u u' : ℝ} (hu1 : u < 1) (hu'0 : 0 < u') (hlt : u' < u)
    (hcap : 1 - u' ≤ 4 * p * (1 - p)) (k : ℕ) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (4 / (u - u'))
        * (ptn_qnorm p (1 + (1 - u') / (4 * p * (1 - p)))
            (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 := by
  have hu'1 : u' < 1 := by linarith
  have hdpos : 0 < u - u' := by linarith
  have hconv := bkt2f_degreeWeight_le_undegree (p := p) hu1 hlt φ k
  have htgt := bkt2f_targetWeight_levelGe2 hp0 hp1 φ hu'0 hu'1 hcap k
  calc 4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (S.card : ℝ) * (1 - u) ^ (S.card - 1)
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ 4 * ((1 / (u - u')) * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (1 - u') ^ S.card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) :=
        mul_le_mul_of_nonneg_left hconv (by norm_num)
    _ ≤ 4 * ((1 / (u - u'))
          * (ptn_qnorm p (1 + (1 - u') / (4 * p * (1 - p)))
              (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left htgt
        positivity
    _ = (4 / (u - u'))
          * (ptn_qnorm p (1 + (1 - u') / (4 * p * (1 - p)))
              (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 := by ring




theorem bkt2f_qnormPow_indicator {p q : ℝ} (hq : 0 < q) (φ : ConfigSpace ι → Bool) :
    ptn_qnormPow p q (fun ω => if φ ω then (1 : ℝ) else 0)
      = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  unfold ptn_qnormPow OSSS.expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : φ ω <;> simp [h, Real.one_rpow, Real.zero_rpow (ne_of_gt hq)]




theorem bkt2f_qnorm_indicator_sq {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {q : ℝ} (hq : 0 < q)
    (φ : ConfigSpace ι → Bool) :
    (ptn_qnorm p q (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2
      = (OSSS.expect (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0)) ^ ((2 : ℝ) / q) := by
  set μ := OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hμ
  have hμnn : 0 ≤ μ := by
    rw [hμ]; unfold OSSS.expect
    exact Finset.sum_nonneg fun ω _ => mul_nonneg
      (Finset.prod_nonneg fun e _ => (bernoulliWeight_isProbWeight hp0 hp1).nonneg e (ω e)) (by positivity)
  unfold ptn_qnorm
  rw [bkt2f_qnormPow_indicator hq φ, ← hμ]
  rw [show (μ ^ (1 / q)) ^ 2 = (μ ^ (1 / q)) ^ (2 : ℝ) from by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
  rw [← Real.rpow_mul hμnn]
  congr 1; field_simp





















def bkt2f_meanInflResidue (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      ∀ u : ℝ, 0 < u → u < 1 →
        ∃ u' : ℝ, 0 < u' ∧ u' < u ∧ 1 - u' ≤ 4 * p * (1 - p) ∧ ∃ k : ℕ, 1 ≤ k ∧
          (4 / (u - u'))
            * (ptn_qnorm p (1 + (1 - u') / (4 * p * (1 - p)))
                (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2
            ≤ (4 * (ptn_sigma p) ^ 2)
                * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
                    ^ (u / (2 - u))
                  - (1 - u) ^ k)
                * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
              - 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1),
                  (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2










theorem bkt2f_levelGe2_of_meanInfl {q : ℝ} (H : bkt2f_meanInflResidue q) :
    bkt2_levelGe2MasterResidue q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  obtain ⟨u', hu'0, hlt, hcap, k, hk1, hbudget⟩ := H p hp hp1 φ u hu0 hu1
  refine ⟨k, hk1, ?_⟩
  
  have hFS := bkt2f_FS_highDegree hp0 hp1 φ hu1 hu'0 hlt hcap k
  
  exact le_trans hFS hbudget






theorem bkt2f_remaining_of_meanInfl {q : ℝ} (H : bkt2f_meanInflResidue q) :
    bkt2_RemainingGoal q :=
  bkt2c_remaining_of_levelGe2 (bkt2f_levelGe2_of_meanInfl H)







theorem bkt2f_master_of_meanInfl {q : ℝ} (H : bkt2f_meanInflResidue q) :
    pro_PBiasedMaster q :=
  bkt2_master_of_remaining (bkt2f_remaining_of_meanInfl H)






theorem bkt2f_rhoOptimise_of_meanInfl {q : ℝ} (H : bkt2f_meanInflResidue q) :
    ptn_RhoOptimise q :=
  bkt2_rhoOptimise_of_remaining (bkt2f_remaining_of_meanInfl H)













theorem bkt2f_meanInflResidue_c0 {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    {u : ℝ} (hu1 : u < 1) (hcap : 1 - 4 * p * (1 - p) < u)
    (hδ0 : 0 < (maxInfl (OSSS.bernoulliWeight p)
        (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
        ^ (u / (2 - u))) :
    ∃ u' : ℝ, 0 < u' ∧ u' < u ∧ 1 - u' ≤ 4 * p * (1 - p) ∧ ∃ k : ℕ, 1 ≤ k ∧
      (4 / (u - u'))
        * (ptn_qnorm p (1 + (1 - u') / (4 * p * (1 - p)))
            (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)) ^ 2
        ≤ (4 * (ptn_sigma p) ^ 2)
            * ((maxInfl (OSSS.bernoulliWeight p)
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
                ^ (u / (2 - u))
              - (1 - u) ^ k)
            * totalInfl (OSSS.bernoulliWeight p)
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)
          - 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1),
              (ptn_coeff p (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) S) ^ 2 := by
  have hp0 : 0 < p := by linarith
  set f0 : ConfigSpace E → Bool := fun _ => false with hf0
  set s := 4 * p * (1 - p) with hs
  have hs0 : 0 < s := by rw [hs]; nlinarith
  have hs1 : s < 1 := by
    rw [hs]; have hne : (1 - 2 * p) ≠ 0 := by intro h; nlinarith [h]
    nlinarith [sq_nonneg (1 - 2 * p), (pow_two_pos_of_ne_zero hne)]
  have h1ms : (0 : ℝ) < 1 - s := by linarith
  have hu0 : 0 < u := lt_trans h1ms hcap
  
  have h1u : (1 : ℝ) - u < 1 := by linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (x := (maxInfl (OSSS.bernoulliWeight p)
      (fun ω => if f0 ω then (1 : ℝ) else 0)) ^ (u / (2 - u))) hδ0 h1u
  
  set u' : ℝ := ((1 - s) + u) / 2 with hu'
  have hu'pos : 0 < u' := by rw [hu']; linarith
  have hu'lt : u' < u := by rw [hu']; linarith
  have hu'cap : 1 - u' ≤ s := by rw [hu']; linarith
  refine ⟨u', hu'pos, hu'lt, by rw [hs] at hu'cap ⊢; linarith [hu'cap], k + 1, by omega, ?_⟩
  
  have hq'pos : (0 : ℝ) < 1 + (1 - u') / s := by
    have : 0 ≤ (1 - u') / s := by
      apply div_nonneg _ hs0.le; nlinarith [hu'cap, hs1]
    linarith
  have hf0zero : (fun ω => if f0 ω then (1 : ℝ) else 0) = (fun _ : ConfigSpace E => (0 : ℝ)) := by
    funext ω; rw [hf0]; simp
  have hμ0 : OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if f0 ω then (1 : ℝ) else 0) = 0 := by
    rw [hf0zero]; unfold OSSS.expect; simp
  have hlhs0 : (ptn_qnorm p (1 + (1 - u') / s)
      (fun ω => if f0 ω then (1 : ℝ) else 0)) ^ 2 = 0 := by
    rw [bkt2f_qnorm_indicator_sq hp0.le hp1.le hq'pos f0, hμ0]
    rw [Real.zero_rpow (by positivity)]
  rw [show (4 / (u - u'))
      * (ptn_qnorm p (1 + (1 - u') / (4 * p * (1 - p)))
          (fun ω => if f0 ω then (1 : ℝ) else 0)) ^ 2 = 0 from by rw [← hs, hlhs0]; ring]
  
  have hcoeff0 : ∀ S : Finset E, ptn_coeff p (fun ω => if f0 ω then (1 : ℝ) else 0) S = 0 := by
    intro S; rw [hf0zero]; unfold ptn_coeff OSSS.expect; simp
  have hz1 : (4 : ℝ) * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1),
      (ptn_coeff p (fun ω => if f0 ω then (1 : ℝ) else 0) S) ^ 2 = 0 := by
    rw [Finset.sum_eq_zero (fun S _ => by rw [hcoeff0]; ring), mul_zero]
  rw [hz1, sub_zero]
  
  have hmono : (1 - u) ^ (k + 1) ≤ (1 - u) ^ k :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
  apply mul_nonneg
  · apply mul_nonneg (by positivity)
    linarith [hk, hmono]
  · exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _







theorem bkt2f_gap_vanishes_at_p_half {u : ℝ} (d : ℕ) :
    (1 - u) ^ (d - 1) - (((1 - u) * (4 * (1/2 : ℝ) * (1 - 1/2))) ^ (d - 1)) = 0 := by
  rw [bkt2_target_eq_damped_of_p_half d]; ring

end StatMech.Probability
