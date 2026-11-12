/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationSpinGauge










namespace StatMech.Onsager

open BigOperators

theorem ons_turnProduct_surgery_sign
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (dir : E → Fin 4) (hdir : ∀ e, dir (rev e) = dir e + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (hI : omega ^ 2 = Complex.I)
    (e : E) (loop : Fin n → E)
    (hloop : (∃ i, loop i = e) ∧ (∃ j, loop j = rev e)) :
    (∏ k, ons_turnW omega
        (dir (ons_surgery e rev loop (k + 1)))
        (dir (ons_surgery e rev loop k))) =
      -∏ k, ons_turnW omega (dir (loop (k + 1))) (dir (loop k)) := by
  let l := ons_l e rev loop
  let m := ons_m e rev loop
  have hlm : l ≤ m := ons_l_le_m hrev hloop
  have hlm' : l < m := by
    rcases lt_or_eq_of_le hlm with h | h
    · exact h
    · have hvm := ons_v_m hrev hloop
      have heq : loop m = loop l := congrArg loop h.symm
      rw [heq] at hvm
      have hfix : rev (loop l) = loop l := hvm.symm
      have hdirs := congrArg dir hfix
      rw [hdir] at hdirs
      generalize hmu : dir (loop l) = mu at hdirs
      fin_cases mu <;> simp at hdirs
  let surgery := ons_surgery e rev loop
  have hs : surgery = ons_revSeg rev l m loop :=
    ons_surgery_eq_revSeg hloop
  let T : Finset (Fin n) :=
    Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m)
  let original : Fin n → ℂ := fun k ↦
    ons_turnW omega (dir (loop (k + 1))) (dir (loop k))
  let reversed : Fin n → ℂ := fun k ↦
    ons_turnW omega (dir (surgery (k + 1))) (dir (surgery k))
  let Q : ℂ := ∏ k ∈ T, original k
  have hlmv : l.val < m.val := hlm'
  have hmn : m.val < n := m.isLt
  have hn2 : 2 ≤ n := by omega
  have hadd1 : ∀ k : Fin n, k.val + 1 < n →
      ((k + 1 : Fin n)).val = k.val + 1 := by
    intro k hk
    rw [Fin.val_add, Fin.val_one',
      Nat.mod_eq_of_lt (by omega : (1 : ℕ) < n), Nat.mod_eq_of_lt hk]
  have soff : ∀ p : Fin n, ¬ (l < p ∧ p < m) →
      surgery p = loop p := by
    intro p hp
    rw [hs]
    by_cases hin : l ≤ p ∧ p ≤ m
    · have hple : p = l ∨ p = m := by
        by_contra hc
        rw [not_or] at hc
        exact hp ⟨lt_of_le_of_ne hin.1 (Ne.symm hc.1),
          lt_of_le_of_ne hin.2 hc.2⟩
      rcases hple with rfl | rfl
      · rw [ons_revSeg_inside rev loop (le_refl _) hlm,
          ons_mir_l hlm, ons_v_m hrev hloop, hrev]
      · rw [ons_revSeg_inside rev loop hlm (le_refl _),
          ons_mir_m hlm]
        exact (ons_v_m hrev hloop).symm
    · exact ons_revSeg_outside rev loop hin
  have factor_off : ∀ k : Fin n, ¬ (l ≤ k ∧ k < m) →
      reversed k = original k := by
    intro k hk
    have h0 : surgery k = loop k := by
      apply soff
      rintro ⟨hlk, hkm⟩
      exact hk ⟨le_of_lt hlk, hkm⟩
    have h1 : surgery (k + 1) = loop (k + 1) := by
      apply soff
      rintro ⟨hlk, hkm⟩
      apply hk
      by_cases hkn : k.val + 1 < n
      · have hv : (k + 1 : Fin n).val = k.val + 1 := hadd1 k hkn
        have hlkv : l.val < (k + 1 : Fin n).val := hlk
        have hkmv : (k + 1 : Fin n).val < m.val := hkm
        rw [hv] at hlkv hkmv
        exact ⟨by show l.val ≤ k.val; omega,
          by show k.val < m.val; omega⟩
      · have hwrap : (k + 1 : Fin n).val = 0 := by
          have heq : k.val + 1 = n := by have := k.isLt; omega
          rw [Fin.val_add, Fin.val_one',
            Nat.mod_eq_of_lt (by omega : (1 : ℕ) < n), heq, Nat.mod_self]
        have hlkv : l.val < (k + 1 : Fin n).val := hlk
        rw [hwrap] at hlkv
        omega
    simp [reversed, original, h0, h1]
  have hsigmaMem : ∀ k ∈ T, ons_mir l m (k + 1) ∈ T := by
    intro k hk
    rw [show T = Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) from rfl,
      Finset.mem_filter] at hk ⊢
    have hk1 : (k + 1 : Fin n).val = k.val + 1 := hadd1 k (by omega)
    have hval : (ons_mir l m (k + 1)).val =
        l.val + m.val - (k.val + 1) := by
      rw [ons_mir_val (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega), hk1]
    exact ⟨Finset.mem_univ _, by show l.val ≤ _; rw [hval]; omega,
      by show _ < m.val; rw [hval]; omega⟩
  have hsigmaInv : ∀ k ∈ T,
      ons_mir l m (ons_mir l m (k + 1) + 1) = k := by
    intro k hk
    rw [show T = Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) from rfl,
      Finset.mem_filter] at hk
    have hk1 : (k + 1 : Fin n).val = k.val + 1 := hadd1 k (by omega)
    have hsig : (ons_mir l m (k + 1)).val =
        l.val + m.val - (k.val + 1) := by
      rw [ons_mir_val (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega), hk1]
    have hsig1 : (ons_mir l m (k + 1) + 1 : Fin n).val =
        l.val + m.val - k.val := by
      rw [hadd1 _ (by rw [hsig]; omega), hsig]
      omega
    apply Fin.ext
    rw [ons_mir_val (by show l.val ≤ _; rw [hsig1]; omega)
      (by show _ ≤ m.val; rw [hsig1]; omega), hsig1]
    omega
  have hreindex :
      (∏ k ∈ T, original (ons_mir l m (k + 1))) = Q := by
    rw [show Q = ∏ k ∈ T, original k from rfl]
    exact Finset.prod_bij'
      (fun k _ ↦ ons_mir l m (k + 1))
      (fun k _ ↦ ons_mir l m (k + 1))
      hsigmaMem hsigmaMem hsigmaInv hsigmaInv (fun k hk ↦ rfl)
  have factor_in : ∀ k ∈ T,
      reversed k = (original (ons_mir l m (k + 1)))⁻¹ := by
    intro k hk
    rw [show T = Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) from rfl,
      Finset.mem_filter] at hk
    have hk1 : (k + 1 : Fin n).val = k.val + 1 := hadd1 k (by omega)
    have hmk : (ons_mir l m k).val = l.val + m.val - k.val :=
      ons_mir_val hk.2.1 (le_of_lt hk.2.2)
    have hmk1 : (ons_mir l m (k + 1)).val =
        l.val + m.val - (k.val + 1) := by
      rw [ons_mir_val (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega), hk1]
    have hnext : ons_mir l m (k + 1) + 1 = ons_mir l m k := by
      apply Fin.ext
      rw [hadd1 _ (by rw [hmk1]; omega), hmk1, hmk]
      omega
    have hsk : surgery k = rev (loop (ons_mir l m k)) := by
      rw [hs]
      exact ons_revSeg_inside rev loop hk.2.1 (le_of_lt hk.2.2)
    have hsk1 : surgery (k + 1) =
        rev (loop (ons_mir l m (k + 1))) := by
      rw [hs]
      exact ons_revSeg_inside rev loop
        (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega)
    simp only [reversed, original, hsk, hsk1, hdir, hnext]
    exact ons_turnW_rev omega _ _
  have hinside : (∏ k ∈ T, reversed k) = Q⁻¹ := by
    rw [Finset.prod_congr rfl factor_in, Finset.prod_inv_distrib,
      hreindex]
  have hQsq : Q ≠ 0 → Q ^ 2 = -1 := by
    intro hQ
    set N : ℕ := m.val - l.val with hN_def
    have hd_bound : ∀ j : Fin (N + 1), l.val + j.val < n := by
      intro j
      have := j.isLt
      omega
    set d : Fin (N + 1) → Fin 4 := fun j ↦
      dir (loop ⟨l.val + j.val, hd_bound j⟩) with hd_def
    have hpbound : ∀ j : Fin N, l.val + j.val < n := by
      intro j
      have := j.isLt
      omega
    have hp_mem : ∀ j : Fin N,
        (⟨l.val + j.val, hpbound j⟩ : Fin n) ∈ T := by
      intro j
      rw [show T = Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) from rfl,
        Finset.mem_filter]
      have := j.isLt
      exact ⟨Finset.mem_univ _, by show l.val ≤ l.val + j.val; omega,
        by show l.val + j.val < m.val; omega⟩
    have hp1 : ∀ j : Fin N,
        ((⟨l.val + j.val, hpbound j⟩ : Fin n) + 1).val =
          l.val + j.val + 1 := by
      intro j
      rw [hadd1 (⟨l.val + j.val, hpbound j⟩ : Fin n)
        (by show l.val + j.val + 1 < n; have := j.isLt; omega)]
    have hdc : ∀ j : Fin N,
        d j.castSucc = dir (loop ⟨l.val + j.val, hpbound j⟩) := by
      intro j
      have he :
          (⟨l.val + (Fin.castSucc j).val, hd_bound (Fin.castSucc j)⟩ : Fin n) =
            ⟨l.val + j.val, hpbound j⟩ := by
        apply Fin.ext
        simp
      simp only [hd_def]
      rw [he]
    have hds : ∀ j : Fin N,
        d j.succ =
          dir (loop ((⟨l.val + j.val, hpbound j⟩ : Fin n) + 1)) := by
      intro j
      have he :
          (⟨l.val + (Fin.succ j).val, hd_bound (Fin.succ j)⟩ : Fin n) =
            (⟨l.val + j.val, hpbound j⟩ : Fin n) + 1 := by
        apply Fin.ext
        simp only [hp1, Fin.val_succ]
        omega
      simp only [hd_def]
      rw [he]
    have hut : ∀ mu : Fin 4, ons_turnW omega (mu + 2) mu = 0 := by
      intro mu
      have h := ons_turnW_uturn omega (mu + 2)
      rwa [show mu + 2 + 2 = mu from by fin_cases mu <;> decide] at h
    have hreindexN :
        (∏ k ∈ T, original k) =
          ∏ j : Fin N, ons_turnW omega (d j.succ) (d j.castSucc) := by
      refine (Finset.prod_bij
        (fun j _ ↦ (⟨l.val + j.val, hpbound j⟩ : Fin n))
        ?_ ?_ ?_ ?_).symm
      · intro j _
        exact hp_mem j
      · intro j1 _ j2 _ heq
        apply Fin.ext
        have hv : l.val + j1.val = l.val + j2.val := congrArg Fin.val heq
        omega
      · intro k hk
        rw [show T = Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) from rfl,
          Finset.mem_filter] at hk
        have h1 : l.val ≤ k.val := hk.2.1
        have h2 : k.val < m.val := hk.2.2
        refine ⟨⟨k.val - l.val, by omega⟩, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        change l.val + (k.val - l.val) = k.val
        omega
      · intro j _
        simp only [original]
        rw [hds j, hdc j]
    have hturnsq :
        (∏ k ∈ T, original k) ^ 2 = -1 := by
      rw [hreindexN]
      refine ons_interior_turn_sq omega homega hI N d ?_ ?_
      · intro j
        have hknz :
            ons_turnW omega
              (dir (loop ((⟨l.val + j.val, hpbound j⟩ : Fin n) + 1)))
              (dir (loop (⟨l.val + j.val, hpbound j⟩ : Fin n))) ≠ 0 := by
          intro hz
          apply hQ
          exact show Q = 0 by
            apply Finset.prod_eq_zero (hp_mem j)
            simpa only [original] using hz
        rw [hds j, hdc j]
        intro hc
        apply hknz
        rw [hc]
        exact hut _
      · have hlast : d (Fin.last N) = dir (loop m) := by
          have he :
              (⟨l.val + (Fin.last N).val,
                hd_bound (Fin.last N)⟩ : Fin n) = m := by
            apply Fin.ext
            simp [Fin.val_last]
            omega
          simp only [hd_def]
          rw [he]
        have hzero : d 0 = dir (loop l) := by
          have he :
              (⟨l.val + (0 : Fin (N + 1)).val, hd_bound 0⟩ : Fin n) = l := by
            apply Fin.ext
            simp
          simp only [hd_def]
          rw [he]
        rw [hlast, hzero, ons_v_m hrev hloop, hdir]
    simpa only [Q] using hturnsq
  have hinsideSign : (∏ k ∈ T, reversed k) =
      -∏ k ∈ T, original k := by
    rw [hinside, show (∏ k ∈ T, original k) = Q from rfl]
    by_cases hQ : Q = 0
    · simp [hQ]
    · have hsq := hQsq hQ
      calc
        Q⁻¹ = Q⁻¹ * 1 := by ring
        _ = Q⁻¹ * (-(Q ^ 2)) := by rw [hsq]; ring
        _ = -(Q⁻¹ * Q) * Q := by rw [pow_two]; ring
        _ = -Q := by rw [inv_mul_cancel₀ hQ]; ring
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun k ↦ l ≤ k ∧ k < m) reversed,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun k ↦ l ≤ k ∧ k < m) original]
  have houtside :
      (∏ k ∈ Finset.univ.filter (fun k ↦ ¬ (l ≤ k ∧ k < m)),
          reversed k) =
        ∏ k ∈ Finset.univ.filter (fun k ↦ ¬ (l ≤ k ∧ k < m)),
          original k := by
    apply Finset.prod_congr rfl
    intro k hk
    exact factor_off k (Finset.mem_filter.mp hk).2
  rw [show Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) = T from rfl,
    hinsideSign, houtside]
  ring




theorem ons_reversibleFactorProduct_surgery
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (dir : E → Fin 4) (hdir : ∀ e, dir (rev e) = dir e + 2)
    (q : E → E → ℂ)
    (hq : ∀ x y, q (rev y) (rev x) = q x y)
    (e : E) (loop : Fin n → E)
    (hloop : (∃ i, loop i = e) ∧ (∃ j, loop j = rev e)) :
    (∏ k, q (ons_surgery e rev loop k)
        (ons_surgery e rev loop (k + 1))) =
      ∏ k, q (loop k) (loop (k + 1)) := by
  let l := ons_l e rev loop
  let m := ons_m e rev loop
  have hlm : l ≤ m := ons_l_le_m hrev hloop
  have hlm' : l < m := by
    rcases lt_or_eq_of_le hlm with h | h
    · exact h
    · have hvm := ons_v_m hrev hloop
      have heq : loop m = loop l := congrArg loop h.symm
      rw [heq] at hvm
      have hfix : rev (loop l) = loop l := hvm.symm
      have hdirs := congrArg dir hfix
      rw [hdir] at hdirs
      generalize hmu : dir (loop l) = mu at hdirs
      fin_cases mu <;> simp at hdirs
  let surgery := ons_surgery e rev loop
  have hs : surgery = ons_revSeg rev l m loop :=
    ons_surgery_eq_revSeg hloop
  let T : Finset (Fin n) :=
    Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m)
  let original : Fin n → ℂ := fun k ↦ q (loop k) (loop (k + 1))
  let reversed : Fin n → ℂ := fun k ↦
    q (surgery k) (surgery (k + 1))
  have hlmv : l.val < m.val := hlm'
  have hmn : m.val < n := m.isLt
  have hn2 : 2 ≤ n := by omega
  have hadd1 : ∀ k : Fin n, k.val + 1 < n →
      ((k + 1 : Fin n)).val = k.val + 1 := by
    intro k hk
    rw [Fin.val_add, Fin.val_one',
      Nat.mod_eq_of_lt (by omega : (1 : ℕ) < n), Nat.mod_eq_of_lt hk]
  have soff : ∀ p : Fin n, ¬ (l < p ∧ p < m) →
      surgery p = loop p := by
    intro p hp
    rw [hs]
    by_cases hin : l ≤ p ∧ p ≤ m
    · have hple : p = l ∨ p = m := by
        by_contra hc
        rw [not_or] at hc
        exact hp ⟨lt_of_le_of_ne hin.1 (Ne.symm hc.1),
          lt_of_le_of_ne hin.2 hc.2⟩
      rcases hple with rfl | rfl
      · rw [ons_revSeg_inside rev loop (le_refl _) hlm,
          ons_mir_l hlm, ons_v_m hrev hloop, hrev]
      · rw [ons_revSeg_inside rev loop hlm (le_refl _),
          ons_mir_m hlm]
        exact (ons_v_m hrev hloop).symm
    · exact ons_revSeg_outside rev loop hin
  have factor_off : ∀ k : Fin n, ¬ (l ≤ k ∧ k < m) →
      reversed k = original k := by
    intro k hk
    have h0 : surgery k = loop k := by
      apply soff
      rintro ⟨hlk, hkm⟩
      exact hk ⟨le_of_lt hlk, hkm⟩
    have h1 : surgery (k + 1) = loop (k + 1) := by
      apply soff
      rintro ⟨hlk, hkm⟩
      apply hk
      by_cases hkn : k.val + 1 < n
      · have hv : (k + 1 : Fin n).val = k.val + 1 := hadd1 k hkn
        have hlkv : l.val < (k + 1 : Fin n).val := hlk
        have hkmv : (k + 1 : Fin n).val < m.val := hkm
        rw [hv] at hlkv hkmv
        exact ⟨by show l.val ≤ k.val; omega,
          by show k.val < m.val; omega⟩
      · have hwrap : (k + 1 : Fin n).val = 0 := by
          have heq : k.val + 1 = n := by have := k.isLt; omega
          rw [Fin.val_add, Fin.val_one',
            Nat.mod_eq_of_lt (by omega : (1 : ℕ) < n), heq, Nat.mod_self]
        have hlkv : l.val < (k + 1 : Fin n).val := hlk
        rw [hwrap] at hlkv
        omega
    simp [reversed, original, h0, h1]
  have hsigmaMem : ∀ k ∈ T, ons_mir l m (k + 1) ∈ T := by
    intro k hk
    rw [show T = Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) from rfl,
      Finset.mem_filter] at hk ⊢
    have hk1 : (k + 1 : Fin n).val = k.val + 1 := hadd1 k (by omega)
    have hval : (ons_mir l m (k + 1)).val =
        l.val + m.val - (k.val + 1) := by
      rw [ons_mir_val (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega), hk1]
    exact ⟨Finset.mem_univ _, by show l.val ≤ _; rw [hval]; omega,
      by show _ < m.val; rw [hval]; omega⟩
  have hsigmaInv : ∀ k ∈ T,
      ons_mir l m (ons_mir l m (k + 1) + 1) = k := by
    intro k hk
    rw [show T = Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) from rfl,
      Finset.mem_filter] at hk
    have hk1 : (k + 1 : Fin n).val = k.val + 1 := hadd1 k (by omega)
    have hsig : (ons_mir l m (k + 1)).val =
        l.val + m.val - (k.val + 1) := by
      rw [ons_mir_val (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega), hk1]
    have hsig1 : (ons_mir l m (k + 1) + 1 : Fin n).val =
        l.val + m.val - k.val := by
      rw [hadd1 _ (by rw [hsig]; omega), hsig]
      omega
    apply Fin.ext
    rw [ons_mir_val (by show l.val ≤ _; rw [hsig1]; omega)
      (by show _ ≤ m.val; rw [hsig1]; omega), hsig1]
    omega
  have hreindex :
      (∏ k ∈ T, original (ons_mir l m (k + 1))) =
        ∏ k ∈ T, original k := by
    exact Finset.prod_bij'
      (fun k _ ↦ ons_mir l m (k + 1))
      (fun k _ ↦ ons_mir l m (k + 1))
      hsigmaMem hsigmaMem hsigmaInv hsigmaInv (fun k hk ↦ rfl)
  have factor_in : ∀ k ∈ T,
      reversed k = original (ons_mir l m (k + 1)) := by
    intro k hk
    rw [show T = Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) from rfl,
      Finset.mem_filter] at hk
    have hk1 : (k + 1 : Fin n).val = k.val + 1 := hadd1 k (by omega)
    have hmk : (ons_mir l m k).val = l.val + m.val - k.val :=
      ons_mir_val hk.2.1 (le_of_lt hk.2.2)
    have hmk1 : (ons_mir l m (k + 1)).val =
        l.val + m.val - (k.val + 1) := by
      rw [ons_mir_val (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega), hk1]
    have hnext : ons_mir l m (k + 1) + 1 = ons_mir l m k := by
      apply Fin.ext
      rw [hadd1 _ (by rw [hmk1]; omega), hmk1, hmk]
      omega
    have hsk : surgery k = rev (loop (ons_mir l m k)) := by
      rw [hs]
      exact ons_revSeg_inside rev loop hk.2.1 (le_of_lt hk.2.2)
    have hsk1 : surgery (k + 1) =
        rev (loop (ons_mir l m (k + 1))) := by
      rw [hs]
      exact ons_revSeg_inside rev loop
        (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega)
    simp only [reversed, original, hsk, hsk1, hnext]
    exact hq _ _
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun k ↦ l ≤ k ∧ k < m) reversed,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun k ↦ l ≤ k ∧ k < m) original]
  have hinside : (∏ k ∈ T, reversed k) = ∏ k ∈ T, original k := by
    rw [Finset.prod_congr rfl factor_in, hreindex]
  have houtside :
      (∏ k ∈ Finset.univ.filter (fun k ↦ ¬ (l ≤ k ∧ k < m)),
          reversed k) =
        ∏ k ∈ Finset.univ.filter (fun k ↦ ¬ (l ≤ k ∧ k < m)),
          original k := by
    apply Finset.prod_congr rfl
    intro k hk
    exact factor_off k (Finset.mem_filter.mp hk).2
  rw [show Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) = T from rfl,
    hinside, houtside]



noncomputable def ons_reversibleTurnMatrix
    {E : Type*} (dir : E → Fin 4) (omega : ℂ)
    (q : E → E → ℂ) : Matrix E E ℂ :=
  fun x y ↦ q x y * ons_turnW omega (dir y) (dir x)

theorem ons_reversibleTurnMatrix_surgery_sign
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (dir : E → Fin 4) (hdir : ∀ e, dir (rev e) = dir e + 2)
    (omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (q : E → E → ℂ)
    (hq : ∀ x y, q (rev y) (rev x) = q x y)
    (e : E) (loop : Fin n → E)
    (hloop : (∃ i, loop i = e) ∧ (∃ j, loop j = rev e)) :
    ons_loopWeight (ons_reversibleTurnMatrix dir omega q)
        (ons_surgery e rev loop) =
      -ons_loopWeight (ons_reversibleTurnMatrix dir omega q) loop := by
  unfold ons_loopWeight ons_reversibleTurnMatrix
  simp_rw [Finset.prod_mul_distrib]
  rw [ons_reversibleFactorProduct_surgery rev hrev dir hdir q hq e loop hloop,
    ons_turnProduct_surgery_sign rev hrev dir hdir omega homega hI e loop hloop]
  ring



theorem ons_reversibleTurnMatrix_lemma5
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (dir : E → Fin 4) (hdir : ∀ e, dir (rev e) = dir e + 2)
    (omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (q : E → E → ℂ)
    (hq : ∀ x y, q (rev y) (rev x) = q x y)
    (e : E) (hrne : rev e ≠ e) :
    ∑ loop ∈ ons_loopSetBoth (n := n) e (rev e),
        ons_loopWeight (ons_reversibleTurnMatrix dir omega q) loop = 0 := by
  apply ons_lemma5 _ e rev hrev hrne
  intro loop hloop
  apply ons_reversibleTurnMatrix_surgery_sign
      rev hrev dir hdir omega homega hI q hq e loop
  simpa only [ons_mem_loopSetBoth] using hloop



theorem ons_invariantStateProduct_surgery
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (weight : E → ℂ) (hweight : ∀ x, weight (rev x) = weight x)
    (e : E) (loop : Fin n → E)
    (hloop : (∃ i, loop i = e) ∧ (∃ j, loop j = rev e)) :
    (∏ k, weight (ons_surgery e rev loop k)) =
      ∏ k, weight (loop k) := by
  let l := ons_l e rev loop
  let m := ons_m e rev loop
  have hlm : l ≤ m := ons_l_le_m hrev hloop
  let surgery := ons_surgery e rev loop
  have hs : surgery = ons_revSeg rev l m loop :=
    ons_surgery_eq_revSeg hloop
  let U : Finset (Fin n) :=
    Finset.univ.filter (fun k ↦ l ≤ k ∧ k ≤ m)
  let P : ℂ := ∏ k ∈ U, weight (loop k)
  have hmirror : (∏ k ∈ U, weight (loop (ons_mir l m k))) = P := by
    rw [show P = ∏ k ∈ U, weight (loop k) from rfl]
    refine Finset.prod_bij'
      (fun k _ ↦ ons_mir l m k) (fun k _ ↦ ons_mir l m k)
      ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have hk' : l ≤ k ∧ k ≤ m := by
        simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      change ons_mir l m k ∈ U
      simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using
        ons_mir_mem hk'.1 hk'.2
    · intro k hk
      have hk' : l ≤ k ∧ k ≤ m := by
        simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      change ons_mir l m k ∈ U
      simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using
        ons_mir_mem hk'.1 hk'.2
    · intro k hk
      have hk' : l ≤ k ∧ k ≤ m := by
        simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      exact ons_mir_mir hk'.1 hk'.2
    · intro k hk
      have hk' : l ≤ k ∧ k ≤ m := by
        simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      exact ons_mir_mir hk'.1 hk'.2
    · intro k _
      rfl
  have hinside : (∏ k ∈ U, weight (surgery k)) = P := by
    calc
      (∏ k ∈ U, weight (surgery k)) =
          ∏ k ∈ U, weight (loop (ons_mir l m k)) := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [show U = Finset.univ.filter (fun k ↦ l ≤ k ∧ k ≤ m) from rfl,
          Finset.mem_filter] at hk
        have hsk : surgery k = rev (loop (ons_mir l m k)) := by
          rw [hs]
          exact ons_revSeg_inside rev loop hk.2.1 hk.2.2
        rw [hsk, hweight]
      _ = P := hmirror
  have houtside :
      (∏ k ∈ Finset.univ.filter (fun k ↦ ¬ (l ≤ k ∧ k ≤ m)),
          weight (surgery k)) =
        ∏ k ∈ Finset.univ.filter (fun k ↦ ¬ (l ≤ k ∧ k ≤ m)),
          weight (loop k) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [Finset.mem_filter] at hk
    have hsk : surgery k = loop k := by
      rw [hs]
      exact ons_revSeg_outside rev loop hk.2
    rw [hsk]
  calc
    (∏ k, weight (surgery k)) =
        (∏ k ∈ U, weight (surgery k)) *
          ∏ k ∈ Finset.univ.filter (fun k ↦ ¬ (l ≤ k ∧ k ≤ m)),
            weight (surgery k) := by
      rw [show U = Finset.univ.filter (fun k ↦ l ≤ k ∧ k ≤ m) from rfl,
        Finset.prod_filter_mul_prod_filter_not]
    _ = P * ∏ k ∈ Finset.univ.filter (fun k ↦ ¬ (l ≤ k ∧ k ≤ m)),
          weight (loop k) := by rw [hinside, houtside]
    _ = ∏ k, weight (loop k) := by
      rw [show P = ∏ k ∈ U, weight (loop k) from rfl,
        show U = Finset.univ.filter (fun k ↦ l ≤ k ∧ k ≤ m) from rfl,
        Finset.prod_filter_mul_prod_filter_not]



noncomputable def ons_stateWeightedReversibleTurnMatrix
    {E : Type*} (dir : E → Fin 4) (omega : ℂ)
    (rowWeight colWeight : E → ℂ) (q : E → E → ℂ) :
    Matrix E E ℂ :=
  fun x y ↦ rowWeight x * colWeight y * q x y *
    ons_turnW omega (dir y) (dir x)

theorem ons_loopWeight_stateWeightedReversibleTurnMatrix
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (dir : E → Fin 4) (omega : ℂ)
    (rowWeight colWeight : E → ℂ) (q : E → E → ℂ)
    (loop : Fin n → E) :
    ons_loopWeight
        (ons_stateWeightedReversibleTurnMatrix
          dir omega rowWeight colWeight q) loop =
      (∏ k, rowWeight (loop k) * colWeight (loop k)) *
        (∏ k, q (loop k) (loop (k + 1))) *
          ∏ k, ons_turnW omega (dir (loop (k + 1))) (dir (loop k)) := by
  have hcol : (∏ k, colWeight (loop (k + 1))) =
      ∏ k, colWeight (loop k) :=
    Equiv.prod_comp (Equiv.addRight (1 : Fin n))
      (fun k ↦ colWeight (loop k))
  unfold ons_loopWeight ons_stateWeightedReversibleTurnMatrix
  rw [show (∏ k, rowWeight (loop k) * colWeight (loop (k + 1)) *
        q (loop k) (loop (k + 1)) *
          ons_turnW omega (dir (loop (k + 1))) (dir (loop k))) =
      (∏ k, rowWeight (loop k)) *
        (∏ k, colWeight (loop (k + 1))) *
        (∏ k, q (loop k) (loop (k + 1))) *
        ∏ k, ons_turnW omega (dir (loop (k + 1))) (dir (loop k)) by
      simp_rw [Finset.prod_mul_distrib]]
  rw [hcol, ← Finset.prod_mul_distrib]

theorem ons_stateWeightedReversibleTurnMatrix_surgery_sign
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (dir : E → Fin 4) (hdir : ∀ e, dir (rev e) = dir e + 2)
    (omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (rowWeight colWeight : E → ℂ)
    (hweight : ∀ x,
      rowWeight (rev x) * colWeight (rev x) =
        rowWeight x * colWeight x)
    (q : E → E → ℂ)
    (hq : ∀ x y, q (rev y) (rev x) = q x y)
    (e : E) (loop : Fin n → E)
    (hloop : (∃ i, loop i = e) ∧ (∃ j, loop j = rev e)) :
    ons_loopWeight
        (ons_stateWeightedReversibleTurnMatrix
          dir omega rowWeight colWeight q)
        (ons_surgery e rev loop) =
      -ons_loopWeight
        (ons_stateWeightedReversibleTurnMatrix
          dir omega rowWeight colWeight q) loop := by
  rw [ons_loopWeight_stateWeightedReversibleTurnMatrix,
    ons_loopWeight_stateWeightedReversibleTurnMatrix]
  rw [ons_invariantStateProduct_surgery rev hrev
      (fun x ↦ rowWeight x * colWeight x) hweight e loop hloop,
    ons_reversibleFactorProduct_surgery rev hrev dir hdir q hq e loop hloop,
    ons_turnProduct_surgery_sign rev hrev dir hdir omega homega hI e loop hloop]
  ring

theorem ons_stateWeightedReversibleTurnMatrix_lemma5
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (dir : E → Fin 4) (hdir : ∀ e, dir (rev e) = dir e + 2)
    (omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (rowWeight colWeight : E → ℂ)
    (hweight : ∀ x,
      rowWeight (rev x) * colWeight (rev x) =
        rowWeight x * colWeight x)
    (q : E → E → ℂ)
    (hq : ∀ x y, q (rev y) (rev x) = q x y)
    (e : E) (hrne : rev e ≠ e) :
    ∑ loop ∈ ons_loopSetBoth (n := n) e (rev e),
        ons_loopWeight
          (ons_stateWeightedReversibleTurnMatrix
            dir omega rowWeight colWeight q) loop = 0 := by
  apply ons_lemma5 _ e rev hrev hrne
  intro loop hloop
  apply ons_stateWeightedReversibleTurnMatrix_surgery_sign
      rev hrev dir hdir omega homega hI
      rowWeight colWeight hweight q hq e loop
  simpa only [ons_mem_loopSetBoth] using hloop




theorem ons_cyclicTurnProduct_omega_inv
    {n : ℕ} [NeZero n] (omega : ℂ)
    (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (d : Fin n → Fin 4) :
    (∏ k, ons_turnW omega⁻¹ (d (k + 1)) (d k)) =
      ∏ k, ons_turnW omega (d (k + 1)) (d k) := by
  by_cases hu : ∃ k : Fin n, d k = d (k + 1) + 2
  · obtain ⟨k, hk⟩ := hu
    have hzInv : ons_turnW omega⁻¹ (d (k + 1)) (d k) = 0 := by
      rw [hk]
      exact ons_turnW_uturn omega⁻¹ _
    have hz : ons_turnW omega (d (k + 1)) (d k) = 0 := by
      rw [hk]
      exact ons_turnW_uturn omega _
    rw [Finset.prod_eq_zero (Finset.mem_univ k) hzInv,
      Finset.prod_eq_zero (Finset.mem_univ k) hz]
  · push_neg at hu
    have hp : (∏ k, ons_turnW omega (d (k + 1)) (d k)) =
        omega ^ (∑ k, ons_turnPow (d (k + 1)) (d k)) := by
      rw [← ons_prod_zpow omega homega]
      exact Finset.prod_congr rfl
        (fun k _ ↦ ons_turnW_eq_zpow omega _ _ (hu k))
    have hpInv : (∏ k, ons_turnW omega⁻¹ (d (k + 1)) (d k)) =
        omega⁻¹ ^ (∑ k, ons_turnPow (d (k + 1)) (d k)) := by
      rw [← ons_prod_zpow omega⁻¹ (inv_ne_zero homega)]
      exact Finset.prod_congr rfl
        (fun k _ ↦ ons_turnW_eq_zpow omega⁻¹ _ _ (hu k))
    rw [hp, hpInv]
    set S := ∑ k, ons_turnPow (d (k + 1)) (d k) with hS
    have hScast : ((S : ℤ) : ZMod 4) = 0 := by
      have hterm : ∀ k : Fin n,
          (((ons_turnPow (d (k + 1)) (d k) : ℤ)) : ZMod 4) =
            ((d k : Fin 4) : ZMod 4) -
              ((d (k + 1) : Fin 4) : ZMod 4) := by
        intro k
        rw [ons_turnPow_cast _ _ (hu k)]
        rfl
      have hshift : (∑ k, ((d (k + 1) : Fin 4) : ZMod 4)) =
          ∑ k, ((d k : Fin 4) : ZMod 4) :=
        Equiv.sum_comp (Equiv.addRight (1 : Fin n))
          (fun k ↦ ((d k : Fin 4) : ZMod 4))
      rw [hS, Int.cast_sum]
      calc
        (∑ k, ((ons_turnPow (d (k + 1)) (d k) : ℤ) : ZMod 4)) =
            ∑ k, (((d k : Fin 4) : ZMod 4) -
              ((d (k + 1) : Fin 4) : ZMod 4)) :=
          Finset.sum_congr rfl (fun k _ ↦ hterm k)
        _ = (∑ k, ((d k : Fin 4) : ZMod 4)) -
            ∑ k, ((d (k + 1) : Fin 4) : ZMod 4) := by
          rw [Finset.sum_sub_distrib]
        _ = 0 := by rw [hshift, sub_self]
    obtain ⟨m, hm⟩ : ∃ m : ℤ, S = 4 * m := by
      obtain ⟨m, hm⟩ :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd S 4).mp hScast
      exact ⟨m, by exact_mod_cast hm⟩
    have h4 : omega ^ (4 : ℤ) = -1 := by
      rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact ons_omega_pow_four omega hI
    rw [hm, _root_.zpow_mul, _root_.zpow_mul,
      _root_.inv_zpow, h4]
    simp

def ons_involutiveLoopRev
    {E : Type*} {n : ℕ} [NeZero n]
    (rev : E → E) (loop : Fin n → E) : Fin n → E :=
  fun k ↦ rev (loop (-k))

theorem ons_involutiveLoopRev_involutive
    {E : Type*} {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (loop : Fin n → E) :
    ons_involutiveLoopRev rev (ons_involutiveLoopRev rev loop) = loop := by
  funext k
  simpa only [ons_involutiveLoopRev, neg_neg] using hrev (loop k)

theorem ons_visits_involutiveLoopRev
    {E : Type*} {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (loop : Fin n → E) (e : E) :
    (∃ i, ons_involutiveLoopRev rev loop i = e) ↔
      ∃ i, loop i = rev e := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨-i, ?_⟩
    have h := congrArg rev hi
    change rev (rev (loop (-i))) = rev e at h
    rw [hrev (loop (-i))] at h
    exact h
  · rintro ⟨i, hi⟩
    refine ⟨-i, ?_⟩
    simp only [ons_involutiveLoopRev, neg_neg, hi]
    exact hrev e

theorem ons_loopWeight_stateWeightedReversibleTurnMatrix_loopRev
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (rev : E → E)
    (dir : E → Fin 4) (hdir : ∀ e, dir (rev e) = dir e + 2)
    (omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (rowWeight colWeight : E → ℂ)
    (hweight : ∀ x,
      rowWeight (rev x) * colWeight (rev x) =
        rowWeight x * colWeight x)
    (q : E → E → ℂ)
    (hq : ∀ x y, q (rev y) (rev x) = q x y)
    (loop : Fin n → E) :
    ons_loopWeight
        (ons_stateWeightedReversibleTurnMatrix
          dir omega rowWeight colWeight q)
        (ons_involutiveLoopRev rev loop) =
      ons_loopWeight
        (ons_stateWeightedReversibleTurnMatrix
          dir omega rowWeight colWeight q) loop := by
  rw [ons_loopWeight_stateWeightedReversibleTurnMatrix,
    ons_loopWeight_stateWeightedReversibleTurnMatrix]
  have hstate :
      (∏ k, rowWeight (ons_involutiveLoopRev rev loop k) *
          colWeight (ons_involutiveLoopRev rev loop k)) =
        ∏ k, rowWeight (loop k) * colWeight (loop k) := by
    calc
      (∏ k, rowWeight (ons_involutiveLoopRev rev loop k) *
          colWeight (ons_involutiveLoopRev rev loop k)) =
          ∏ k, rowWeight (loop (-k)) * colWeight (loop (-k)) := by
        apply Finset.prod_congr rfl
        intro k hk
        exact hweight _
      _ = ∏ k, rowWeight (loop k) * colWeight (loop k) :=
        Equiv.prod_comp (Equiv.neg (Fin n))
          (fun k ↦ rowWeight (loop k) * colWeight (loop k))
  have hqprod :
      (∏ k, q (ons_involutiveLoopRev rev loop k)
          (ons_involutiveLoopRev rev loop (k + 1))) =
        ∏ k, q (loop k) (loop (k + 1)) := by
    calc
      (∏ k, q (ons_involutiveLoopRev rev loop k)
          (ons_involutiveLoopRev rev loop (k + 1))) =
          ∏ k, q (loop (-(k + 1))) (loop (-k)) := by
        apply Finset.prod_congr rfl
        intro k hk
        exact hq _ _
      _ = ∏ k, q (loop k) (loop (k + 1)) := by
        rw [← Equiv.prod_comp
          ((Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n)))
          (fun j ↦ q (loop j) (loop (j + 1)))]
        apply Finset.prod_congr rfl
        intro k hk
        have hrho :
            ((Equiv.addRight (1 : Fin n)).trans
              (Equiv.neg (Fin n))) k = -(k + 1) := rfl
        rw [hrho]
        have hk1 : (-(k + 1) + 1 : Fin n) = -k := by abel
        rw [hk1]
  have hturn :
      (∏ k, ons_turnW omega
          (dir (ons_involutiveLoopRev rev loop (k + 1)))
          (dir (ons_involutiveLoopRev rev loop k))) =
        ∏ k, ons_turnW omega (dir (loop (k + 1))) (dir (loop k)) := by
    calc
      (∏ k, ons_turnW omega
          (dir (ons_involutiveLoopRev rev loop (k + 1)))
          (dir (ons_involutiveLoopRev rev loop k))) =
          ∏ k, ons_turnW omega⁻¹
            (dir (loop (-k))) (dir (loop (-(k + 1)))) := by
        apply Finset.prod_congr rfl
        intro k hk
        simp only [ons_involutiveLoopRev, hdir]
        rw [ons_turnW_rev, ons_turnW_omega_inv]
      _ = ∏ k, ons_turnW omega⁻¹
          (dir (loop (k + 1))) (dir (loop k)) := by
        rw [← Equiv.prod_comp
          ((Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n)))
          (fun j ↦ ons_turnW omega⁻¹
            (dir (loop (j + 1))) (dir (loop j)))]
        apply Finset.prod_congr rfl
        intro k hk
        have hrho :
            ((Equiv.addRight (1 : Fin n)).trans
              (Equiv.neg (Fin n))) k = -(k + 1) := rfl
        rw [hrho]
        have hk1 : (-(k + 1) + 1 : Fin n) = -k := by abel
        rw [hk1]
      _ = _ := ons_cyclicTurnProduct_omega_inv omega homega hI
        (fun k ↦ dir (loop k))
  rw [hstate, hqprod, hturn]

noncomputable def ons_maskedReversibleFactor
    {E : Type*} [DecidableEq E]
    (forbidden : Finset E) (q : E → E → ℂ) : E → E → ℂ :=
  fun x y ↦ if x ∈ forbidden ∨ y ∈ forbidden then 0 else q x y

theorem ons_mask_stateWeightedReversibleTurnMatrix
    {E : Type*} [Fintype E] [DecidableEq E]
    (forbidden : Finset E)
    (dir : E → Fin 4) (omega : ℂ)
    (rowWeight colWeight : E → ℂ) (q : E → E → ℂ) :
    ons_maskMatrix forbidden
        (ons_stateWeightedReversibleTurnMatrix
          dir omega rowWeight colWeight q) =
      ons_stateWeightedReversibleTurnMatrix dir omega rowWeight colWeight
        (ons_maskedReversibleFactor forbidden q) := by
  ext x y
  simp only [ons_maskMatrix, ons_stateWeightedReversibleTurnMatrix,
    ons_maskedReversibleFactor]
  split <;> ring

theorem ons_maskedReversibleFactor_rev
    {E : Type*} [DecidableEq E]
    (rev : E → E) (forbidden : Finset E)
    (hforbidden : ∀ x, rev x ∈ forbidden ↔ x ∈ forbidden)
    (q : E → E → ℂ)
    (hq : ∀ x y, q (rev y) (rev x) = q x y)
    (x y : E) :
    ons_maskedReversibleFactor forbidden q (rev y) (rev x) =
      ons_maskedReversibleFactor forbidden q x y := by
  unfold ons_maskedReversibleFactor
  simp only [hforbidden y, hforbidden x]
  by_cases h : x ∈ forbidden ∨ y ∈ forbidden
  · have h' : y ∈ forbidden ∨ x ∈ forbidden := h.elim Or.inr Or.inl
    rw [if_pos h, if_pos h']
  · have h' : ¬ (y ∈ forbidden ∨ x ∈ forbidden) := by tauto
    rw [if_neg h, if_neg h', hq]

end StatMech.Onsager
