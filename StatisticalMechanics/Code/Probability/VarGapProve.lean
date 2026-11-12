/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Code.Probability.VarGapClose
import Code.Probability.FullRangeHC
import Code.Probability.RhoOptimiseEngine

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





theorem vgp_val_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (b : Bool) :
    ptn_val b = p + ptn_sigma p * ptn_psi p b := by
  unfold ptn_psi
  have hσ : ptn_sigma p ≠ 0 := (ptn_sigma_pos hp0 hp1).ne'
  rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hσ, mul_one]; ring




theorem vgp_dictator_expansion {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (e₀ : ι) :
    (fun ω : ConfigSpace ι => if (fun ω => ω e₀) ω then (1 : ℝ) else 0)
      = fun ω => p * ptn_pchar p (∅ : Finset ι) ω
          + ptn_sigma p * ptn_pchar p ({e₀} : Finset ι) ω := by
  funext ω
  simp only
  have hval : (if ω e₀ then (1 : ℝ) else 0) = ptn_val (ω e₀) := by
    unfold ptn_val; rfl
  rw [hval, vgp_val_eq hp0 hp1]
  rw [ptn_pchar_empty]
  have hsing : ptn_pchar p ({e₀} : Finset ι) ω = ptn_psi p (ω e₀) := by
    unfold ptn_pchar; rw [Finset.prod_singleton]
  rw [hsing]; ring



theorem vgp_dictator_coeff {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (e₀ : ι) (S : Finset ι) :
    ptn_coeff p (fun ω : ConfigSpace ι => if (fun ω => ω e₀) ω then (1 : ℝ) else 0) S
      = if S = (∅ : Finset ι) then p else if S = {e₀} then ptn_sigma p else 0 := by
  unfold ptn_coeff
  rw [vgp_dictator_expansion hp0 hp1 e₀]
  
  have hexp : (fun ω : ConfigSpace ι =>
        (p * ptn_pchar p (∅ : Finset ι) ω + ptn_sigma p * ptn_pchar p ({e₀} : Finset ι) ω)
          * ptn_pchar p S ω)
      = fun ω => p * (ptn_pchar p (∅ : Finset ι) ω * ptn_pchar p S ω)
          + ptn_sigma p * (ptn_pchar p ({e₀} : Finset ι) ω * ptn_pchar p S ω) := by
    funext ω; ring
  rw [hexp]
  rw [OSSS.expect_add, OSSS.expect_const_mul, OSSS.expect_const_mul,
      ptn_orthonormal hp0 hp1, ptn_orthonormal hp0 hp1]
  
  have hne : ({e₀} : Finset ι) ≠ (∅ : Finset ι) := Finset.singleton_ne_empty e₀
  by_cases h1 : S = (∅ : Finset ι)
  · subst h1
    rw [if_pos rfl, if_pos rfl, if_neg hne, mul_one, mul_zero, add_zero]
  · rw [if_neg h1]
    by_cases h2 : S = {e₀}
    · subst h2
      rw [if_neg (fun h => hne h.symm), if_pos rfl, if_pos rfl, mul_zero, zero_add, mul_one]
    · rw [if_neg h2, if_neg (fun h => h1 h.symm), if_neg (fun h => h2 h.symm),
          mul_zero, mul_zero, add_zero]






theorem vgp_dictator_var {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    OSSS.var (OSSS.bernoulliWeight p)
        (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)
      = p * (1 - p) := by
  set f := fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0 with hf
  rw [ptn_var_eq_fourierWeight hp0 hp1 f]
  have hcoeff : ∀ S : Finset (Fin 1), ptn_coeff p f S
      = if S = (∅ : Finset (Fin 1)) then p else if S = {0} then ptn_sigma p else 0 := by
    intro S; rw [hf]; exact vgp_dictator_coeff hp0 hp1 0 S
  
  have herase : (univ.erase (∅ : Finset (Fin 1))) = {({0} : Finset (Fin 1))} := by decide
  rw [herase, Finset.sum_singleton, hcoeff,
      if_neg (Finset.singleton_ne_empty (0 : Fin 1)), if_pos rfl, ptn_sigma_sq hp0 hp1]



theorem vgp_dictator_totalInfl {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    totalInfl (OSSS.bernoulliWeight p)
        (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)
      = 1 := by
  set f := fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0 with hf
  have hσ2 : (ptn_sigma p) ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have hσ2pos : 0 < (ptn_sigma p) ^ 2 := by rw [hσ2]; nlinarith
  rw [ptn_totalInfl_eq_fourierWeight hp0 hp1]
  have hcoeff : ∀ S : Finset (Fin 1), ptn_coeff p f S
      = if S = (∅ : Finset (Fin 1)) then p else if S = {0} then ptn_sigma p else 0 := by
    intro S; rw [hf]; exact vgp_dictator_coeff hp0 hp1 0 S
  
  have huniv : (univ : Finset (Finset (Fin 1))) = {(∅ : Finset (Fin 1)), {0}} := by decide
  rw [huniv, Finset.sum_pair (by decide : (∅ : Finset (Fin 1)) ≠ {0})]
  rw [hcoeff, hcoeff, if_pos rfl, if_neg (Finset.singleton_ne_empty (0 : Fin 1)), if_pos rfl]
  simp only [Finset.card_empty, Nat.cast_zero, Finset.card_singleton, Nat.cast_one, zero_mul,
    one_mul, zero_add]
  rw [hσ2, one_div]
  exact inv_mul_cancel₀ (by nlinarith : (p * (1 - p)) ≠ 0)



theorem vgp_maxInfl_eq_totalInfl_fin1 (p : ℝ) (φ : ConfigSpace (Fin 1) → Bool) :
    maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      = totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω : ConfigSpace (Fin 1) => if φ ω then (1 : ℝ) else 0 with hf
  
  have hmax : maxInfl (OSSS.bernoulliWeight p) f = OSSS.infl (OSSS.bernoulliWeight p) f 0 := by
    unfold maxInfl
    apply le_antisymm
    · apply Finset.sup'_le; intro e _
      have : e = (0 : Fin 1) := Subsingleton.elim e 0
      rw [this]
    · exact Finset.le_sup' _ (Finset.mem_univ 0)
  have htot : totalInfl (OSSS.bernoulliWeight p) f = OSSS.infl (OSSS.bernoulliWeight p) f 0 := by
    unfold totalInfl
    rw [Finset.sum_eq_single (0 : Fin 1)]
    · intro e _ he; exact absurd (Subsingleton.elim e 0) he
    · intro h; exact absurd (Finset.mem_univ 0) h
  rw [hmax, htot]



theorem vgp_dictator_maxInfl {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    maxInfl (OSSS.bernoulliWeight p)
        (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)
      = 1 := by
  rw [vgp_maxInfl_eq_totalInfl_fin1, vgp_dictator_totalInfl hp0 hp1]



theorem vgp_dictator_meanVar {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)
      * (1 - OSSS.expect (OSSS.bernoulliWeight p)
          (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0))
      = p * (1 - p) := by
  have hvar := vgp_dictator_var hp0 hp1
  rw [mil_var_eq (fun ω : ConfigSpace (Fin 1) => (fun ω => ω 0) ω)] at hvar
  rw [← hvar]; ring



theorem vgp_dictator_level1 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∑ S ∈ univ.filter (fun S : Finset (Fin 1) => S.card = 1),
        (ptn_coeff p (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) S) ^ 2
      = p * (1 - p) := by
  have hfilter : (univ.filter (fun S : Finset (Fin 1) => S.card = 1))
      = {({0} : Finset (Fin 1))} := by decide
  rw [hfilter, Finset.sum_singleton, vgp_dictator_coeff hp0 hp1 0,
      if_neg (Finset.singleton_ne_empty (0 : Fin 1)), if_pos rfl, ptn_sigma_sq hp0 hp1]



























theorem vgp_varPowerCore_refutable {q : ℝ} (hq : 1 / 2 < q) :
    ¬ vgc_VarPowerCore q := by
  intro H
  
  set p := (1 / 2 + min q 1) / 2 with hpdef
  have hqgt : (1 / 2 : ℝ) < min q 1 := lt_min hq (by norm_num)
  have hp_lo : 1 / 2 < p := by rw [hpdef]; linarith [hqgt]
  have hp_hi : p < min q 1 := by rw [hpdef]; linarith [hqgt]
  have hp_q : p < q := lt_of_lt_of_le hp_hi (min_le_left _ _)
  have hp_1 : p < 1 := lt_of_lt_of_le hp_hi (min_le_right _ _)
  have hp0 : 0 < p := by linarith
  have hmem : p ∈ Set.Ioo (1 / 2 : ℝ) q := ⟨hp_lo, hp_q⟩
  
  set φ : ConfigSpace (Fin 1) → Bool := fun ω => ω 0 with hφ
  have hδ1 : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 1 :=
    vgp_dictator_maxInfl hp0 hp_1
  have hδpos : 0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
    rw [hδ1]; norm_num
  have hbound := @H p hmem hp_1 (Fin 1) _ _ _ φ (1 / 2) (by norm_num) (by norm_num) hδpos
  
  rw [vgp_dictator_meanVar hp0 hp_1] at hbound
  rw [hδ1, Real.one_rpow] at hbound
  rw [vgp_dictator_totalInfl hp0 hp_1] at hbound
  rw [ptn_sigma_sq hp0 hp_1] at hbound
  
  have hσ2pos : 0 < p * (1 - p) := by nlinarith
  
  have hfac : ((1 : ℝ) / 2) / (4 + 2 * (1 / 2)) = 1 / 10 := by norm_num
  rw [hfac] at hbound
  
  nlinarith [hbound, hσ2pos]





















theorem vgp_varGapCore_refutable {q : ℝ} (hq : 1 / 2 < q) :
    ¬ bkt2p_VarGapCore q := by
  intro H
  set p := (1 / 2 + min q 1) / 2 with hpdef
  have hqgt : (1 / 2 : ℝ) < min q 1 := lt_min hq (by norm_num)
  have hp_lo : 1 / 2 < p := by rw [hpdef]; linarith [hqgt]
  have hp_hi : p < min q 1 := by rw [hpdef]; linarith [hqgt]
  have hp_q : p < q := lt_of_lt_of_le hp_hi (min_le_left _ _)
  have hp_1 : p < 1 := lt_of_lt_of_le hp_hi (min_le_right _ _)
  have hp0 : 0 < p := by linarith
  have hmem : p ∈ Set.Ioo (1 / 2 : ℝ) q := ⟨hp_lo, hp_q⟩
  set φ : ConfigSpace (Fin 1) → Bool := fun ω => ω 0 with hφ
  
  obtain ⟨u', hu'0, hu'lt, k, hk1, hbound⟩ :=
    @H p hmem hp_1 (Fin 1) _ _ _ φ (1 / 2) (by norm_num) (by norm_num)
  
  rw [vgp_dictator_meanVar hp0 hp_1, vgp_dictator_maxInfl hp0 hp_1, Real.one_rpow,
      vgp_dictator_totalInfl hp0 hp_1, vgp_dictator_level1 hp0 hp_1, ptn_sigma_sq hp0 hp_1] at hbound
  have hσ2pos : 0 < p * (1 - p) := by nlinarith
  
  have hLHSpos : 0 < (4 / (1 / 2 - u')) * (p * (1 - p)) := by
    apply mul_pos _ hσ2pos
    apply div_pos (by norm_num); linarith [hu'lt]
  have h1uk : (0 : ℝ) ≤ (1 - (1 : ℝ) / 2) ^ k := by positivity
  
  have hRHS : 4 * (p * (1 - p)) * (1 - (1 - (1:ℝ) / 2) ^ k) * 1 - 4 * (p * (1 - p))
      = -(4 * (p * (1 - p)) * (1 - (1:ℝ) / 2) ^ k) := by ring
  rw [hRHS] at hbound
  nlinarith [hbound, hLHSpos, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hσ2pos.le) h1uk]






theorem vgp_poincare_tight_on_dictator {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)
      * (1 - OSSS.expect (OSSS.bernoulliWeight p)
          (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0))
      = (ptn_sigma p) ^ 2
        * totalInfl (OSSS.bernoulliWeight p)
            (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) := by
  rw [vgp_dictator_meanVar hp0 hp1, vgp_dictator_totalInfl hp0 hp1, mul_one, ptn_sigma_sq hp0 hp1]





















theorem vgp_master_holds_on_dictator {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {u : ℝ} (_hu0 : 0 < u) (_hu1 : u < 1) :
    (∑ S : Finset (Fin 1), 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p)
          (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p)
            (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) := by
  set f := fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0 with hf
  have hcoeff : ∀ S : Finset (Fin 1), ptn_coeff p f S
      = if S = (∅ : Finset (Fin 1)) then p else if S = {0} then ptn_sigma p else 0 := by
    intro S; rw [hf]; exact vgp_dictator_coeff hp0 hp1 0 S
  
  have huniv : (univ : Finset (Finset (Fin 1))) = {(∅ : Finset (Fin 1)), {0}} := by decide
  have hLHS : (∑ S : Finset (Fin 1), 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
      * (ptn_coeff p f S) ^ 2) = 4 * (ptn_sigma p) ^ 2 := by
    rw [huniv, Finset.sum_pair (by decide : (∅ : Finset (Fin 1)) ≠ {0})]
    rw [hcoeff, hcoeff, if_pos rfl, if_neg (Finset.singleton_ne_empty (0 : Fin 1)), if_pos rfl]
    simp only [Finset.card_empty, Nat.cast_zero, Finset.card_singleton, Nat.cast_one, mul_zero,
      zero_mul, zero_add]
    ring
  rw [hLHS, vgp_dictator_maxInfl hp0 hp1, Real.one_rpow, vgp_dictator_totalInfl hp0 hp1, mul_one,
      ptn_sigma_sq hp0 hp1]
  
  nlinarith [sq_nonneg (1 - 2 * p)]













theorem vgp_rhoOptimise_of_openResidue {q : ℝ} (H : frh_openResidue q) :
    ptn_RhoOptimise q :=
  mxd_rhoOptimise_of_martingaleHC (frh_martingaleHC_of_openResidue H)















theorem vgp_integral_collapse_logGain
    {E : Type*} [Fintype E] {c : E → ℝ}
    {d : E → ℕ} (hc : ∀ i, 0 ≤ c i) {δ : ℝ} (hδ : 0 ≤ δ)
    (Hmaster : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (∑ i : E, 4 * (d i : ℝ) * (1 - u) ^ (d i - 1) * c i)
        ≤ δ ^ (u / (2 - u)) * (∑ i : E, 4 * (d i : ℝ) * c i)) :
    2 * (∑ i ∈ univ.filter (fun i => d i ≠ 0), c i) * Real.log (1 / δ)
      ≤ ∑ i : E, 4 * (d i : ℝ) * c i :=
  roe_logGain_four hc hδ Hmaster

end StatMech.Probability
