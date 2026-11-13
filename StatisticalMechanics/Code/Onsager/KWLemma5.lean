/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.ShermanLemma5
import Code.Onsager.KWLoopWeight
import Code.Onsager.TurningTelescope
import Code.Onsager.TurnReversal
import Code.Onsager.KWMatrix
import Code.Onsager.ShermanLoop










namespace StatMech.Onsager

open Matrix BigOperators






theorem kw_rev_factor {L : ℕ} (x ω : ℂ) (a b : ons_Dart L) :
    ons_KWmat L x ω (ons_dartRev L a) (ons_dartRev L b)
      = if ons_dirStep L a.2 a.1 = b.1 then x * (ons_turnW ω a.2 b.2)⁻¹ else 0 := by
  unfold ons_KWmat ons_dartRev
  simp only
  rw [ons_dirStep_opposite, ons_turnW_rev]


theorem ons_turnW_swap (ω : ℂ) (μ ν : Fin 4) :
    ons_turnW ω ν μ = (ons_turnW ω μ ν)⁻¹ := by
  fin_cases μ <;> fin_cases ν <;> simp [ons_turnW]





theorem ons_interior_turn_sq (ω : ℂ) (hω : ω ≠ 0) (hI : ω ^ 2 = Complex.I)
    (N : ℕ) (d : Fin (N + 1) → Fin 4)
    (hnu : ∀ k : Fin N, d k.succ ≠ d k.castSucc + 2)
    (hend : d (Fin.last N) = d 0 + 2) :
    (∏ j : Fin N, ons_turnW ω (d j.succ) (d j.castSucc)) ^ 2 = -1 := by
  have hswap : ∀ j : Fin N,
      ons_turnW ω (d j.succ) (d j.castSucc) = (ons_turnW ω (d j.castSucc) (d j.succ))⁻¹ :=
    fun j => ons_turnW_swap ω (d j.castSucc) (d j.succ)
  rw [Finset.prod_congr rfl (fun j _ => hswap j), Finset.prod_inv_distrib]
  obtain ⟨mm, hmm⟩ := ons_walk_prod_antipodal ω hω hI N d hnu hend
  rw [hmm, inv_pow]
  have hsq : ((-1 : ℂ) ^ mm * Complex.I) ^ 2 = -1 := by
    rw [mul_pow]
    have h1 : ((-1 : ℂ) ^ mm) ^ 2 = 1 := by
      rw [← zpow_natCast ((-1 : ℂ) ^ mm) 2, ← _root_.zpow_mul]
      rw [show mm * (2 : ℕ) = 2 * mm from by push_cast; ring, _root_.zpow_mul]
      norm_num
    rw [h1, Complex.I_sq]; ring
  rw [hsq]; norm_num



theorem ons_KW_surgery_sign {L : ℕ} [NeZero L] [Fact (2 < L)]
    {n : ℕ} [NeZero n] (x ω : ℂ) (hω : ω ^ 2 = Complex.I)
    (e : ons_Dart L) (v : Fin n → ons_Dart L)
    (hv : v ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
    ons_loopWeight (ons_KWmat L x ω)
        (ons_surgery e (ons_dartRev L) v) =
      -ons_loopWeight (ons_KWmat L x ω) v := by
  rw [ons_mem_loopSetBoth] at hv
  set rev := ons_dartRev L with hrev_def
  have hrevinv : Function.Involutive rev := ons_dartRev_involutive L
  set l := ons_l e rev v with hl_def
  set m := ons_m e rev v with hm_def
  have hlm : l ≤ m := ons_l_le_m hrevinv hv
  have hvm : v m = rev (v l) := ons_v_m hrevinv hv
  
  have hlm' : l < m := by
    rcases lt_or_eq_of_le hlm with h | h
    · exact h
    · exfalso
      apply ons_dartRev_ne L (v l)
      rw [← hrev_def, ← hvm, h]
  set s := ons_surgery e rev v with hs_def
  have hs : s = ons_revSeg rev l m v := ons_surgery_eq_revSeg hv
  
  simp only [ons_loopWeight]
  
  set fv : Fin n → ℂ := fun k => ons_KWmat L x ω (v k) (v (k + 1)) with hfv_def
  set fs : Fin n → ℂ := fun k => ons_KWmat L x ω (s k) (s (k + 1)) with hfs_def
  show (∏ k, fs k) = - ∏ k, fv k
  
  have hlmv : l.val < m.val := hlm'
  have hmn : m.val < n := m.isLt
  have hn2 : 2 ≤ n := by omega
  have hadd1 : ∀ k : Fin n, k.val + 1 < n → ((k + 1 : Fin n)).val = k.val + 1 := by
    intro k hk
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : (1 : ℕ) < n),
      Nat.mod_eq_of_lt hk]
  
  by_cases hx : x = 0
  · subst hx
    have h0 : ∀ k : Fin n, fs k = 0 := by
      intro k; simp only [hfs_def, ons_KWmat]; split <;> simp
    have h0' : ∀ k : Fin n, fv k = 0 := by
      intro k; simp only [hfv_def, ons_KWmat]; split <;> simp
    rw [Finset.prod_eq_zero (Finset.mem_univ (0 : Fin n)) (h0 0),
      Finset.prod_eq_zero (Finset.mem_univ (0 : Fin n)) (h0' 0)]
    ring
  
  · 
    have soff : ∀ p : Fin n, ¬(l < p ∧ p < m) → s p = v p := by
      intro p hp
      rw [hs]
      by_cases hin : l ≤ p ∧ p ≤ m
      · obtain ⟨hlp, hpm⟩ := hin
        have hple : p = l ∨ p = m := by
          by_contra hc
          rw [not_or] at hc
          exact hp ⟨lt_of_le_of_ne hlp (Ne.symm hc.1), lt_of_le_of_ne hpm hc.2⟩
        rcases hple with rfl | rfl
        · rw [ons_revSeg_inside rev v (le_refl _) hlm, ons_mir_l hlm, hvm, hrevinv]
        · rw [ons_revSeg_inside rev v hlm (le_refl _), ons_mir_m hlm]; exact hvm.symm
      · exact ons_revSeg_outside rev v hin
    
    have factor_off : ∀ k : Fin n, ¬(l ≤ k ∧ k < m) → fs k = fv k := by
      intro k hk
      have h1 : s k = v k := by
        apply soff; rintro ⟨ha, hb⟩; exact hk ⟨le_of_lt ha, hb⟩
      have h2 : s (k + 1) = v (k + 1) := by
        apply soff; rintro ⟨ha, hb⟩
        apply hk
        by_cases hkn : k.val + 1 < n
        · have hval : (k + 1 : Fin n).val = k.val + 1 := hadd1 k hkn
          have hav : l.val < (k + 1 : Fin n).val := ha
          have hbv : (k + 1 : Fin n).val < m.val := hb
          rw [hval] at hav hbv
          exact ⟨by show l.val ≤ k.val; omega, by show k.val < m.val; omega⟩
        · exfalso
          have hkn' : k.val + 1 = n := by have := k.isLt; omega
          have hval0 : (k + 1 : Fin n).val = 0 := by
            rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : (1 : ℕ) < n), hkn',
              Nat.mod_self]
          have hav : l.val < (k + 1 : Fin n).val := ha
          rw [hval0] at hav; omega
      simp only [hfs_def, hfv_def, h1, h2]
    
    set T : Finset (Fin n) := Finset.univ.filter (fun k => l ≤ k ∧ k < m) with hT_def
    set Q : ℂ := ∏ k ∈ T, fv k with hQ_def
    
    have hσmem : ∀ a ∈ T, ons_mir l m (a + 1) ∈ T := by
      intro a ha
      rw [hT_def, Finset.mem_filter] at ha ⊢
      obtain ⟨-, hla, ham⟩ := ha
      have hlav : l.val ≤ a.val := hla
      have hamv : a.val < m.val := ham
      have ha1 : (a + 1 : Fin n).val = a.val + 1 := hadd1 a (by omega)
      have hla1 : l ≤ (a + 1 : Fin n) := by show l.val ≤ _; rw [ha1]; omega
      have ha1m : (a + 1 : Fin n) ≤ m := by show _ ≤ m.val; rw [ha1]; omega
      have hval : (ons_mir l m (a + 1)).val = l.val + m.val - (a.val + 1) := by
        rw [ons_mir_val hla1 ha1m, ha1]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · show l.val ≤ _; rw [hval]; omega
      · show _ < m.val; rw [hval]; omega
    have hσσ : ∀ a ∈ T, ons_mir l m (ons_mir l m (a + 1) + 1) = a := by
      intro a ha
      rw [hT_def, Finset.mem_filter] at ha
      obtain ⟨-, hla, ham⟩ := ha
      have hlav : l.val ≤ a.val := hla
      have hamv : a.val < m.val := ham
      have ha1 : (a + 1 : Fin n).val = a.val + 1 := hadd1 a (by omega)
      have hla1 : l ≤ (a + 1 : Fin n) := by show l.val ≤ _; rw [ha1]; omega
      have ha1m : (a + 1 : Fin n) ≤ m := by show _ ≤ m.val; rw [ha1]; omega
      have hval : (ons_mir l m (a + 1)).val = l.val + m.val - (a.val + 1) := by
        rw [ons_mir_val hla1 ha1m, ha1]
      have hb1 : (ons_mir l m (a + 1) + 1 : Fin n).val = l.val + m.val - a.val := by
        rw [hadd1 _ (by rw [hval]; omega), hval]; omega
      have hlb1 : l ≤ (ons_mir l m (a + 1) + 1 : Fin n) := by show l.val ≤ _; rw [hb1]; omega
      have hb1m : (ons_mir l m (a + 1) + 1 : Fin n) ≤ m := by show _ ≤ m.val; rw [hb1]; omega
      apply Fin.ext
      rw [ons_mir_val hlb1 hb1m, hb1]; omega
    have hσ_reindex : (∏ k ∈ T, fv (ons_mir l m (k + 1))) = Q := by
      rw [hQ_def]
      exact Finset.prod_bij' (fun a _ => ons_mir l m (a + 1)) (fun a _ => ons_mir l m (a + 1))
        hσmem hσmem hσσ hσσ (fun a _ => rfl)
    
    have factor_in : ∀ k ∈ T, fs k = x ^ 2 * (fv (ons_mir l m (k + 1)))⁻¹ := by
      intro k hk
      rw [hT_def, Finset.mem_filter] at hk
      obtain ⟨-, hlk, hkm⟩ := hk
      have hkmv : k.val < m.val := hkm
      have hlkv : l.val ≤ k.val := hlk
      have hkm' : k ≤ m := le_of_lt hkm
      have hk1 : (k + 1 : Fin n).val = k.val + 1 := hadd1 k (by omega)
      have hlk1 : l ≤ (k + 1 : Fin n) := by show l.val ≤ _; rw [hk1]; omega
      have hk1m : (k + 1 : Fin n) ≤ m := by show _ ≤ m.val; rw [hk1]; omega
      have hmirk : (ons_mir l m k).val = l.val + m.val - k.val := ons_mir_val hlk hkm'
      have hsigk : (ons_mir l m (k + 1)).val = l.val + m.val - (k.val + 1) := by
        rw [ons_mir_val hlk1 hk1m, hk1]
      have hsig1 : (ons_mir l m (k + 1) + 1 : Fin n) = ons_mir l m k := by
        apply Fin.ext
        rw [hadd1 _ (by rw [hsigk]; omega), hsigk, hmirk]; omega
      have hsk : s k = rev (v (ons_mir l m k)) := by
        rw [hs]; exact ons_revSeg_inside rev v hlk hkm'
      have hsk1 : s (k + 1) = rev (v (ons_mir l m (k + 1))) := by
        rw [hs]; exact ons_revSeg_inside rev v hlk1 hk1m
      have hfvsig : fv (ons_mir l m (k + 1))
          = ons_KWmat L x ω (v (ons_mir l m (k + 1))) (v (ons_mir l m k)) := by
        simp only [hfv_def]; rw [hsig1]
      simp only [hfs_def]
      rw [hsk, hsk1, hrev_def, kw_rev_factor, hfvsig]
      simp only [ons_KWmat]
      by_cases hcond :
          ons_dirStep L (v (ons_mir l m k)).2 (v (ons_mir l m k)).1 = (v (ons_mir l m (k + 1))).1
      · rw [if_pos hcond, if_pos hcond.symm,
          mul_inv, ← mul_assoc, sq, mul_assoc x x x⁻¹, mul_inv_cancel₀ hx, mul_one]
      · rw [if_neg hcond, if_neg (fun h => hcond h.symm)]
        simp
    
    have hF3 : (∏ k ∈ T, fs k) = x ^ (2 * T.card) * Q⁻¹ := by
      calc ∏ k ∈ T, fs k
          = ∏ k ∈ T, x ^ 2 * (fv (ons_mir l m (k + 1)))⁻¹ :=
            Finset.prod_congr rfl factor_in
        _ = (∏ _k ∈ T, x ^ 2) * ∏ k ∈ T, (fv (ons_mir l m (k + 1)))⁻¹ :=
            Finset.prod_mul_distrib
        _ = x ^ (2 * T.card) * (∏ k ∈ T, fv (ons_mir l m (k + 1)))⁻¹ := by
            rw [Finset.prod_const, Finset.prod_inv_distrib, ← pow_mul]
        _ = x ^ (2 * T.card) * Q⁻¹ := by rw [hσ_reindex]
    
    have hωne : ω ≠ 0 := by
      intro h; rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hω
      exact Complex.I_ne_zero hω.symm
    have hF5 : Q ≠ 0 → Q ^ 2 = - x ^ (2 * T.card) := by
      intro hQ0
      
      have hfvval : ∀ k ∈ T, fv k = x * ons_turnW ω (v (k + 1)).2 (v k).2 := by
        intro k hk
        have hne : fv k ≠ 0 := by
          intro h; exact hQ0 (hQ_def ▸ Finset.prod_eq_zero hk h)
        by_cases hc : (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1
        · simp only [hfv_def, ons_KWmat, if_pos hc]
        · exfalso; apply hne; simp only [hfv_def, ons_KWmat, if_neg hc]
      have hQval : Q = x ^ T.card * ∏ k ∈ T, ons_turnW ω (v (k + 1)).2 (v k).2 := by
        rw [hQ_def, Finset.prod_congr rfl hfvval, Finset.prod_mul_distrib, Finset.prod_const]
      
      set N : ℕ := m.val - l.val with hN_def
      have hd_bound : ∀ j : Fin (N + 1), l.val + j.val < n := by
        intro j; have := j.isLt; omega
      set d : Fin (N + 1) → Fin 4 := fun j => (v ⟨l.val + j.val, hd_bound j⟩).2 with hd_def
      have hpbound : ∀ j : Fin N, l.val + j.val < n := by intro j; have := j.isLt; omega
      
      have hp_mem : ∀ j : Fin N, (⟨l.val + j.val, hpbound j⟩ : Fin n) ∈ T := by
        intro j; rw [hT_def, Finset.mem_filter]
        have := j.isLt
        exact ⟨Finset.mem_univ _, by show l.val ≤ l.val + j.val; omega,
          by show l.val + j.val < m.val; omega⟩
      have hp1 : ∀ j : Fin N, ((⟨l.val + j.val, hpbound j⟩ : Fin n) + 1).val = l.val + j.val + 1 := by
        intro j
        rw [hadd1 (⟨l.val + j.val, hpbound j⟩ : Fin n)
          (by show l.val + j.val + 1 < n; have := j.isLt; omega)]
      have hdc : ∀ j : Fin N, d j.castSucc = (v ⟨l.val + j.val, hpbound j⟩).2 := by
        intro j
        have he : (⟨l.val + (Fin.castSucc j).val, hd_bound (Fin.castSucc j)⟩ : Fin n)
            = ⟨l.val + j.val, hpbound j⟩ := by apply Fin.ext; simp
        simp only [hd_def]; rw [he]
      have hds : ∀ j : Fin N, d j.succ = (v ((⟨l.val + j.val, hpbound j⟩ : Fin n) + 1)).2 := by
        intro j
        have he : (⟨l.val + (Fin.succ j).val, hd_bound (Fin.succ j)⟩ : Fin n)
            = (⟨l.val + j.val, hpbound j⟩ : Fin n) + 1 := by
          apply Fin.ext; simp only [hp1, Fin.val_succ]; omega
        simp only [hd_def]; rw [he]
      
      have hut : ∀ μ : Fin 4, ons_turnW ω (μ + 2) μ = 0 := by
        intro μ
        have h := ons_turnW_uturn ω (μ + 2)
        rwa [show μ + 2 + 2 = μ from by fin_cases μ <;> decide] at h
      
      have hreindex : (∏ k ∈ T, ons_turnW ω (v (k + 1)).2 (v k).2)
          = ∏ j : Fin N, ons_turnW ω (d j.succ) (d j.castSucc) := by
        refine (Finset.prod_bij (fun j _ => (⟨l.val + j.val, hpbound j⟩ : Fin n))
          ?_ ?_ ?_ ?_).symm
        · intro j _; exact hp_mem j
        · intro j₁ _ j₂ _ heq
          apply Fin.ext
          have hv : l.val + j₁.val = l.val + j₂.val := congrArg Fin.val heq
          omega
        · intro k hk
          rw [hT_def, Finset.mem_filter] at hk
          have h1 : l.val ≤ k.val := hk.2.1
          have h2 : k.val < m.val := hk.2.2
          refine ⟨⟨k.val - l.val, by omega⟩, Finset.mem_univ _, ?_⟩
          apply Fin.ext; change l.val + (k.val - l.val) = k.val; omega
        · intro j _; rw [hds j, hdc j]
      have hturnsq : (∏ k ∈ T, ons_turnW ω (v (k + 1)).2 (v k).2) ^ 2 = -1 := by
        rw [hreindex]
        refine ons_interior_turn_sq ω hωne hω N d ?_ ?_
        · 
          intro j
          have hknz : ons_turnW ω (v ((⟨l.val + j.val, hpbound j⟩ : Fin n) + 1)).2
              (v (⟨l.val + j.val, hpbound j⟩ : Fin n)).2 ≠ 0 := by
            have hne : fv (⟨l.val + j.val, hpbound j⟩ : Fin n) ≠ 0 := fun h =>
              hQ0 (hQ_def ▸ Finset.prod_eq_zero (hp_mem j) h)
            rw [hfvval _ (hp_mem j)] at hne
            exact fun h => hne (by rw [h, mul_zero])
          rw [hds j, hdc j]
          intro hc
          apply hknz
          rw [hc]
          exact hut _
        · 
          have hlast : d (Fin.last N) = (v m).2 := by
            have he : (⟨l.val + (Fin.last N).val, hd_bound (Fin.last N)⟩ : Fin n) = m := by
              apply Fin.ext; simp [Fin.val_last]; omega
            simp only [hd_def]; rw [he]
          have hzero : d 0 = (v l).2 := by
            have he : (⟨l.val + (0 : Fin (N + 1)).val, hd_bound 0⟩ : Fin n) = l := by
              apply Fin.ext; simp
            simp only [hd_def]; rw [he]
          rw [hlast, hzero, hvm, hrev_def]; rfl
      rw [hQval, mul_pow, hturnsq, ← pow_mul, mul_comm T.card 2]; ring
    
    have hAQ : (∏ k ∈ T, fs k) = -Q := by
      rw [hF3]
      by_cases hQ0 : Q = 0
      · rw [hQ0]; simp
      · have hxe : x ^ (2 * T.card) = -Q ^ 2 := by
          have := hF5 hQ0; linear_combination this
        rw [hxe, sq, neg_mul, mul_assoc, mul_inv_cancel₀ hQ0, mul_one]
    
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => l ≤ k ∧ k < m) fs,
      ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => l ≤ k ∧ k < m) fv]
    have hReq : (∏ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k < m)), fs k)
        = ∏ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k < m)), fv k := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [Finset.mem_filter] at hk
      exact factor_off k hk.2
    rw [hReq]
    rw [← hT_def, ← hQ_def, hAQ]
    ring


theorem ons_KW_lemma5 {L : ℕ} [NeZero L] [Fact (2 < L)] {n : ℕ} [NeZero n] (x ω : ℂ)
    (hω : ω ^ 2 = Complex.I) (e : ons_Dart L) :
    ∑ v ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e),
      ons_loopWeight (ons_KWmat L x ω) v = 0 := by
  apply ons_lemma5 _ e (ons_dartRev L) (ons_dartRev_involutive L) (ons_dartRev_ne L e)
  intro v hv
  exact ons_KW_surgery_sign x ω hω e v hv

end StatMech.Onsager
