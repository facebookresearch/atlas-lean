/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Code.Probability.VarGapClose

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS





theorem ctc_sum_fin1 (g : ConfigSpace (Fin 1) → ℝ) :
    ∑ ω : ConfigSpace (Fin 1), g ω = g (fun _ => false) + g (fun _ => true) := by
  have : (Finset.univ : Finset (ConfigSpace (Fin 1)))
      = {(fun _ => false), (fun _ => true)} := by
    ext ω
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases h : ω 0
    · right; funext i; fin_cases i; exact h
    · left; funext i; fin_cases i; simpa using h
  rw [this, Finset.sum_insert (by
    simp only [Finset.mem_singleton]
    intro h
    have := congrFun h 0
    simp at this), Finset.sum_singleton]


theorem ctc_weight_false (p : ℝ) :
    OSSS.weight (OSSS.bernoulliWeight p) (fun _ : Fin 1 => false) = 1 - p := by
  unfold OSSS.weight OSSS.bernoulliWeight
  rw [Fin.prod_univ_one]; simp


theorem ctc_weight_true (p : ℝ) :
    OSSS.weight (OSSS.bernoulliWeight p) (fun _ : Fin 1 => true) = p := by
  unfold OSSS.weight OSSS.bernoulliWeight
  rw [Fin.prod_univ_one]; simp



theorem ctc_expect_fin1 (p : ℝ) (g : ConfigSpace (Fin 1) → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) g
      = (1 - p) * g (fun _ => false) + p * g (fun _ => true) := by
  unfold OSSS.expect
  rw [ctc_sum_fin1, ctc_weight_false, ctc_weight_true]




theorem ctc_infl (p : ℝ) :
    OSSS.infl (OSSS.bernoulliWeight p)
        (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) 0 = 1 := by
  unfold OSSS.infl
  rw [ctc_expect_fin1]
  have hopen : ∀ ω : ConfigSpace (Fin 1), (StatMech.setOpen 0 ω) 0 = true := by
    intro ω; rw [StatMech.setOpen]; simp
  have hclosed : ∀ ω : ConfigSpace (Fin 1), (StatMech.setClosed 0 ω) 0 = false := by
    intro ω; rw [StatMech.setClosed]; simp
  simp only [hopen, hclosed]
  norm_num


theorem ctc_totalInfl (p : ℝ) :
    totalInfl (OSSS.bernoulliWeight p)
        (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) = 1 := by
  unfold totalInfl
  rw [Fin.sum_univ_one, ctc_infl]


theorem ctc_maxInfl (p : ℝ) :
    maxInfl (OSSS.bernoulliWeight p)
        (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) = 1 := by
  have hle := kkl_infl_le_maxInfl (OSSS.bernoulliWeight p)
    (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) 0
  rw [ctc_infl] at hle
  refine le_antisymm ?_ hle
  apply Finset.sup'_le
  intro e _
  have : e = 0 := Subsingleton.elim _ _
  subst this; rw [ctc_infl]



theorem ctc_coeff_single (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ptn_coeff p (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) {0}
      = ptn_sigma p := by
  unfold ptn_coeff
  rw [ctc_expect_fin1]
  have hchar : ∀ ω : ConfigSpace (Fin 1), ptn_pchar p {0} ω = ptn_psi p (ω 0) := by
    intro ω; unfold ptn_pchar; rw [Finset.prod_singleton]
  simp only [hchar]
  show (1 - p) * ((if (false : Bool) then (1:ℝ) else 0) * ptn_psi p ((fun _ : Fin 1 => false) 0))
      + p * ((if (true : Bool) then (1:ℝ) else 0) * ptn_psi p ((fun _ : Fin 1 => true) 0))
      = ptn_sigma p
  simp only [if_true, Bool.false_eq_true, if_false, zero_mul, mul_zero, one_mul, zero_add]
  unfold ptn_psi
  simp only [ptn_val_true]
  have hσ : ptn_sigma p ≠ 0 := (ptn_sigma_pos hp0 hp1).ne'
  have hσ2 : ptn_sigma p ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  rw [mul_div_assoc', eq_comm, eq_div_iff hσ]
  nlinarith [hσ2]


theorem ctc_mean (p : ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) = p := by
  rw [ctc_expect_fin1]; simp



theorem ctc_L1 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∑ S ∈ univ.filter (fun S : Finset (Fin 1) => S.card = 1),
        (ptn_coeff p (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) S) ^ 2)
      = (ptn_sigma p) ^ 2 := by
  have hfilter : (univ.filter (fun S : Finset (Fin 1) => S.card = 1)) = {({0} : Finset (Fin 1))} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
      rw [ha]; congr 1; exact Subsingleton.elim a 0
    · intro h; subst h; exact Finset.card_singleton 0
  rw [hfilter, Finset.sum_singleton, ctc_coeff_single p hp0 hp1]



theorem ctc_ge2_empty (k : ℕ) :
    (univ.filter (fun S : Finset (Fin 1) => 2 ≤ S.card ∧ S.card ≤ k)) = ∅ := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro ⟨h2, _⟩
  have : S.card ≤ 1 := by have := Finset.card_le_univ S; simpa using this
  omega













theorem ctc_varPowerCore_false {q : ℝ} (hq : (3:ℝ)/4 < q) :
    ¬ vgc_VarPowerCore q := by
  intro H
  have hp : (3/4 : ℝ) ∈ Set.Ioo (1/2 : ℝ) q := ⟨by norm_num, hq⟩
  have hp1 : (3/4 : ℝ) < 1 := by norm_num
  have hp0 : (0:ℝ) < 3/4 := by norm_num
  set φ : ConfigSpace (Fin 1) → Bool := fun ω => ω 0 with hφ
  have hδpos : (0:ℝ) < maxInfl (OSSS.bernoulliWeight (3/4))
      (fun ω => if φ ω then (1:ℝ) else 0) := by rw [ctc_maxInfl]; norm_num
  have h := H (3/4) hp hp1 φ (1/2) (by norm_num) (by norm_num) hδpos
  rw [ctc_mean, ctc_maxInfl, ctc_totalInfl] at h
  rw [ptn_sigma_sq hp0 hp1, Real.one_rpow] at h
  norm_num at h









theorem ctc_levelGe2_false {q : ℝ} (hq : (3:ℝ)/4 < q) :
    ¬ bkt2_levelGe2MasterResidue q := by
  intro H
  have hp : (3/4 : ℝ) ∈ Set.Ioo (1/2 : ℝ) q := ⟨by norm_num, hq⟩
  have hp1 : (3/4 : ℝ) < 1 := by norm_num
  have hp0 : (0:ℝ) < 3/4 := by norm_num
  set φ : ConfigSpace (Fin 1) → Bool := fun ω => ω 0 with hφ
  obtain ⟨k, hk1, h⟩ := H (3/4) hp hp1 φ (1/2) (by norm_num) (by norm_num)
  rw [ctc_ge2_empty, Finset.sum_empty, ctc_maxInfl, ctc_totalInfl, ctc_L1 _ hp0 hp1] at h
  rw [ptn_sigma_sq hp0 hp1, Real.one_rpow] at h
  have hpowpos : (0:ℝ) < (1 - 1/2)^k := by positivity
  nlinarith [h, hpowpos]




theorem ctc_remainingGoal_false {q : ℝ} (hq : (3:ℝ)/4 < q) :
    ¬ bkt2_RemainingGoal q := by
  intro H
  have hp : (3/4 : ℝ) ∈ Set.Ioo (1/2 : ℝ) q := ⟨by norm_num, hq⟩
  have hp1 : (3/4 : ℝ) < 1 := by norm_num
  have hp0 : (0:ℝ) < 3/4 := by norm_num
  set φ : ConfigSpace (Fin 1) → Bool := fun ω => ω 0 with hφ
  obtain ⟨k, hk1, h⟩ := H (3/4) hp hp1 φ (1/2) (by norm_num) (by norm_num)
  rw [ctc_ge2_empty, Finset.sum_empty, ctc_maxInfl, ctc_totalInfl, ctc_L1 _ hp0 hp1] at h
  rw [ptn_sigma_sq hp0 hp1, Real.one_rpow] at h
  have hpowpos : (0:ℝ) < (1 - 1/2)^k := by positivity
  nlinarith [h, hpowpos]








theorem ctc_varGapCore_false {q : ℝ} (hq : (3:ℝ)/4 < q) :
    ¬ bkt2p_VarGapCore q := by
  intro H
  have hp : (3/4 : ℝ) ∈ Set.Ioo (1/2 : ℝ) q := ⟨by norm_num, hq⟩
  have hp1 : (3/4 : ℝ) < 1 := by norm_num
  have hp0 : (0:ℝ) < 3/4 := by norm_num
  set φ : ConfigSpace (Fin 1) → Bool := fun ω => ω 0 with hφ
  obtain ⟨u', hu'0, hu'u, k, hk1, h⟩ := H (3/4) hp hp1 φ (1/2) (by norm_num) (by norm_num)
  rw [ctc_mean, ctc_maxInfl, ctc_totalInfl, ctc_L1 _ hp0 hp1] at h
  rw [ptn_sigma_sq hp0 hp1, Real.one_rpow] at h
  have hpowpos : (0:ℝ) < (1 - 1/2)^k := by positivity
  have hLHSpos : (0:ℝ) < 4 / (1/2 - u') * (3/4 * (1 - 3/4)) := by
    apply mul_pos
    · exact div_pos (by norm_num) (by linarith)
    · norm_num
  nlinarith [h, hpowpos, hLHSpos]








theorem ctc_varScalarCore_false {q : ℝ} (hq : (3:ℝ)/4 < q) :
    ¬ mil_VarScalarCore q := by
  intro H
  have hp : (3/4 : ℝ) ∈ Set.Ioo (1/2 : ℝ) q := ⟨by norm_num, hq⟩
  have hp1 : (3/4 : ℝ) < 1 := by norm_num
  have hp0 : (0:ℝ) < 3/4 := by norm_num
  set φ : ConfigSpace (Fin 1) → Bool := fun ω => ω 0 with hφ
  obtain ⟨k, hk1, h⟩ := H (3/4) hp hp1 φ (1/2) (by norm_num) (by norm_num)
  rw [ctc_mean, ctc_maxInfl, ctc_totalInfl] at h
  rw [ptn_sigma_sq hp0 hp1, Real.one_rpow] at h
  have hpowpos : (0:ℝ) < (1 - 1/2)^k := by positivity
  have hkge : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
  nlinarith [h, hpowpos, hkge]












theorem ctc_lowDegree_k0_holds (p : ℝ) {u : ℝ} :
    4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 1) => 1 ≤ S.card ∧ S.card ≤ 0),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) S) ^ 2
      ≤ (4 * (ptn_sigma p) ^ 2)
        * ((maxInfl (OSSS.bernoulliWeight p)
              (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0)) ^ (u / (2 - u))
          - (1 - u) ^ (0:ℕ))
        * totalInfl (OSSS.bernoulliWeight p)
            (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1:ℝ) else 0) := by
  have hempty : (univ.filter (fun S : Finset (Fin 1) => 1 ≤ S.card ∧ S.card ≤ 0)) = ∅ := by
    ext S; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    omega
  rw [hempty, Finset.sum_empty, ctc_maxInfl, ctc_totalInfl, Real.one_rpow]
  simp













theorem ctc_variance_family_all_false {q : ℝ} (hq : (3:ℝ)/4 < q) :
    ¬ vgc_VarPowerCore q ∧ ¬ bkt2p_VarGapCore q ∧ ¬ mil_VarScalarCore q
      ∧ ¬ bkt2_levelGe2MasterResidue q ∧ ¬ bkt2_RemainingGoal q :=
  ⟨ctc_varPowerCore_false hq, ctc_varGapCore_false hq, ctc_varScalarCore_false hq,
    ctc_levelGe2_false hq, ctc_remainingGoal_false hq⟩

end StatMech.Probability
