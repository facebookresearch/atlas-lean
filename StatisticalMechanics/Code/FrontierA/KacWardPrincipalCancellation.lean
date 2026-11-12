/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAngleHomotopy
import Code.FrontierA.KacWardFixedMonomialCancellation
import Code.FrontierA.KacWardRectilinearGraphCancellation










open scoped BigOperators

namespace StatMech.FrontierA

open Finset
open SimpleGraph




theorem kw_phaseProduct_surgery_sign
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    {n : ℕ} [NeZero n]
    (reverse : Dart → Dart) (hreverse : Function.Involutive reverse)
    (hreverse_ne : ∀ dart, reverse dart ≠ dart)
    (phase : Dart → Dart → ℂ)
    (valid : Dart → Dart → Prop)
    (hpathSq : ∀ {N : ℕ} (path : Fin (N + 1) → Dart),
      path (Fin.last N) = reverse (path 0) →
        (∀ j : Fin N, valid (path j.castSucc) (path j.succ)) →
        (∏ j : Fin N, phase (path j.castSucc) (path j.succ)) ^ 2 = -1)
    (selected : Dart) (loop : Fin n → Dart)
    (hboth : (∃ i, loop i = selected) ∧
      ∃ j, loop j = reverse selected)
    (hvalid : ∀ k : Fin n, valid (loop k) (loop (k + 1)))
    (hphase : ∀ k : Fin n,
      phase (reverse (loop (k + 1))) (reverse (loop k)) =
        (phase (loop k) (loop (k + 1)))⁻¹) :
    (∏ k, phase
        (StatMech.Onsager.ons_surgery selected reverse loop k)
        (StatMech.Onsager.ons_surgery selected reverse loop (k + 1))) =
      -∏ k, phase (loop k) (loop (k + 1)) := by
  let l := StatMech.Onsager.ons_l selected reverse loop
  let m := StatMech.Onsager.ons_m selected reverse loop
  have hlm : l ≤ m := StatMech.Onsager.ons_l_le_m hreverse hboth
  have hlm' : l < m := by
    rcases lt_or_eq_of_le hlm with h | h
    · exact h
    · have hvm := StatMech.Onsager.ons_v_m hreverse hboth
      have heq : loop m = loop l := congrArg loop h.symm
      rw [heq] at hvm
      exact False.elim (hreverse_ne (loop l) hvm.symm)
  let surgery := StatMech.Onsager.ons_surgery selected reverse loop
  have hs : surgery = StatMech.Onsager.ons_revSeg reverse l m loop :=
    StatMech.Onsager.ons_surgery_eq_revSeg hboth
  let T : Finset (Fin n) :=
    Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m)
  let original : Fin n → ℂ := fun k ↦ phase (loop k) (loop (k + 1))
  let reversed : Fin n → ℂ := fun k ↦
    phase (surgery k) (surgery (k + 1))
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
      · rw [StatMech.Onsager.ons_revSeg_inside reverse loop (le_refl _) hlm,
          StatMech.Onsager.ons_mir_l hlm,
          StatMech.Onsager.ons_v_m hreverse hboth, hreverse]
      · rw [StatMech.Onsager.ons_revSeg_inside reverse loop hlm (le_refl _),
          StatMech.Onsager.ons_mir_m hlm]
        exact (StatMech.Onsager.ons_v_m hreverse hboth).symm
    · exact StatMech.Onsager.ons_revSeg_outside reverse loop hin
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
  have hsigmaMem : ∀ k ∈ T,
      StatMech.Onsager.ons_mir l m (k + 1) ∈ T := by
    intro k hk
    rw [show T = Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) from rfl,
      Finset.mem_filter] at hk ⊢
    have hk1 : (k + 1 : Fin n).val = k.val + 1 := hadd1 k (by omega)
    have hval : (StatMech.Onsager.ons_mir l m (k + 1)).val =
        l.val + m.val - (k.val + 1) := by
      rw [StatMech.Onsager.ons_mir_val
        (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega), hk1]
    exact ⟨Finset.mem_univ _, by show l.val ≤ _; rw [hval]; omega,
      by show _ < m.val; rw [hval]; omega⟩
  have hsigmaInv : ∀ k ∈ T,
      StatMech.Onsager.ons_mir l m
        (StatMech.Onsager.ons_mir l m (k + 1) + 1) = k := by
    intro k hk
    rw [show T = Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) from rfl,
      Finset.mem_filter] at hk
    have hk1 : (k + 1 : Fin n).val = k.val + 1 := hadd1 k (by omega)
    have hsig : (StatMech.Onsager.ons_mir l m (k + 1)).val =
        l.val + m.val - (k.val + 1) := by
      rw [StatMech.Onsager.ons_mir_val
        (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega), hk1]
    have hsig1 :
        (StatMech.Onsager.ons_mir l m (k + 1) + 1 : Fin n).val =
          l.val + m.val - k.val := by
      rw [hadd1 _ (by rw [hsig]; omega), hsig]
      omega
    apply Fin.ext
    rw [StatMech.Onsager.ons_mir_val
      (by show l.val ≤ _; rw [hsig1]; omega)
      (by show _ ≤ m.val; rw [hsig1]; omega), hsig1]
    omega
  have hreindex :
      (∏ k ∈ T,
        original (StatMech.Onsager.ons_mir l m (k + 1))) = Q := by
    rw [show Q = ∏ k ∈ T, original k from rfl]
    exact Finset.prod_bij'
      (fun k _ ↦ StatMech.Onsager.ons_mir l m (k + 1))
      (fun k _ ↦ StatMech.Onsager.ons_mir l m (k + 1))
      hsigmaMem hsigmaMem hsigmaInv hsigmaInv (fun k hk ↦ rfl)
  have factor_in : ∀ k ∈ T,
      reversed k =
        (original (StatMech.Onsager.ons_mir l m (k + 1)))⁻¹ := by
    intro k hk
    rw [show T = Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) from rfl,
      Finset.mem_filter] at hk
    have hk1 : (k + 1 : Fin n).val = k.val + 1 := hadd1 k (by omega)
    have hmk : (StatMech.Onsager.ons_mir l m k).val =
        l.val + m.val - k.val :=
      StatMech.Onsager.ons_mir_val hk.2.1 (le_of_lt hk.2.2)
    have hmk1 : (StatMech.Onsager.ons_mir l m (k + 1)).val =
        l.val + m.val - (k.val + 1) := by
      rw [StatMech.Onsager.ons_mir_val
        (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega), hk1]
    have hnext : StatMech.Onsager.ons_mir l m (k + 1) + 1 =
        StatMech.Onsager.ons_mir l m k := by
      apply Fin.ext
      rw [hadd1 _ (by rw [hmk1]; omega), hmk1, hmk]
      omega
    have hsk : surgery k =
        reverse (loop (StatMech.Onsager.ons_mir l m k)) := by
      rw [hs]
      exact StatMech.Onsager.ons_revSeg_inside reverse loop
        hk.2.1 (le_of_lt hk.2.2)
    have hsk1 : surgery (k + 1) =
        reverse (loop (StatMech.Onsager.ons_mir l m (k + 1))) := by
      rw [hs]
      exact StatMech.Onsager.ons_revSeg_inside reverse loop
        (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega)
    simp only [reversed, original, hsk, hsk1]
    simpa only [hnext] using
      hphase (StatMech.Onsager.ons_mir l m (k + 1))
  have hinside : (∏ k ∈ T, reversed k) = Q⁻¹ := by
    rw [Finset.prod_congr rfl factor_in, Finset.prod_inv_distrib, hreindex]
  have hQsq : Q ^ 2 = -1 := by
    set N : ℕ := m.val - l.val with hN_def
    have hd_bound : ∀ j : Fin (N + 1), l.val + j.val < n := by
      intro j
      have := j.isLt
      omega
    set path : Fin (N + 1) → Dart := fun j ↦
      loop ⟨l.val + j.val, hd_bound j⟩ with hpath_def
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
    have hpc : ∀ j : Fin N,
        path j.castSucc = loop ⟨l.val + j.val, hpbound j⟩ := by
      intro j
      have he :
          (⟨l.val + (Fin.castSucc j).val,
            hd_bound (Fin.castSucc j)⟩ : Fin n) =
            ⟨l.val + j.val, hpbound j⟩ := by
        apply Fin.ext
        simp
      simp only [hpath_def]
      rw [he]
    have hps : ∀ j : Fin N,
        path j.succ =
          loop ((⟨l.val + j.val, hpbound j⟩ : Fin n) + 1) := by
      intro j
      have he :
          (⟨l.val + (Fin.succ j).val,
            hd_bound (Fin.succ j)⟩ : Fin n) =
            (⟨l.val + j.val, hpbound j⟩ : Fin n) + 1 := by
        apply Fin.ext
        simp only [hp1, Fin.val_succ]
        omega
      simp only [hpath_def]
      rw [he]
    have hreindexN :
        (∏ k ∈ T, original k) =
          ∏ j : Fin N, phase (path j.castSucc) (path j.succ) := by
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
        rw [hpc j, hps j]
    rw [show Q = ∏ k ∈ T, original k from rfl, hreindexN]
    apply hpathSq path
    · have hlast : path (Fin.last N) = loop m := by
        have he :
            (⟨l.val + (Fin.last N).val,
              hd_bound (Fin.last N)⟩ : Fin n) = m := by
          apply Fin.ext
          simp [Fin.val_last]
          omega
        simp only [hpath_def]
        rw [he]
      have hzero : path 0 = loop l := by
        have he :
            (⟨l.val + (0 : Fin (N + 1)).val, hd_bound 0⟩ : Fin n) = l := by
          apply Fin.ext
          simp
        simp only [hpath_def]
        rw [he]
      rw [hlast, hzero]
      exact StatMech.Onsager.ons_v_m hreverse hboth
    · intro j
      rw [hpc j, hps j]
      exact hvalid ⟨l.val + j.val, hpbound j⟩
  have hQne : Q ≠ 0 := by
    intro hQ
    rw [hQ] at hQsq
    norm_num at hQsq
  have hinsideSign : (∏ k ∈ T, reversed k) =
      -∏ k ∈ T, original k := by
    rw [hinside, show (∏ k ∈ T, original k) = Q from rfl]
    calc
      Q⁻¹ = Q⁻¹ * 1 := by ring
      _ = Q⁻¹ * (-(Q ^ 2)) := by rw [hQsq]; ring
      _ = -(Q⁻¹ * Q) * Q := by rw [pow_two]; ring
      _ = -Q := by rw [inv_mul_cancel₀ hQne]; ring
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




theorem kw_reversibleFactorProduct_surgery
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    {n : ℕ} [NeZero n]
    (reverse : Dart → Dart) (hreverse : Function.Involutive reverse)
    (hreverse_ne : ∀ dart, reverse dart ≠ dart)
    (factor : Dart → Dart → ℂ)
    (hfactor : ∀ x y, factor (reverse y) (reverse x) = factor x y)
    (selected : Dart) (loop : Fin n → Dart)
    (hboth : (∃ i, loop i = selected) ∧
      ∃ j, loop j = reverse selected) :
    (∏ k, factor
        (StatMech.Onsager.ons_surgery selected reverse loop k)
        (StatMech.Onsager.ons_surgery selected reverse loop (k + 1))) =
      ∏ k, factor (loop k) (loop (k + 1)) := by
  let l := StatMech.Onsager.ons_l selected reverse loop
  let m := StatMech.Onsager.ons_m selected reverse loop
  have hlm : l ≤ m := StatMech.Onsager.ons_l_le_m hreverse hboth
  have hlm' : l < m := by
    rcases lt_or_eq_of_le hlm with h | h
    · exact h
    · have hvm := StatMech.Onsager.ons_v_m hreverse hboth
      have heq : loop m = loop l := congrArg loop h.symm
      rw [heq] at hvm
      exact False.elim (hreverse_ne (loop l) hvm.symm)
  let surgery := StatMech.Onsager.ons_surgery selected reverse loop
  have hs : surgery = StatMech.Onsager.ons_revSeg reverse l m loop :=
    StatMech.Onsager.ons_surgery_eq_revSeg hboth
  let T : Finset (Fin n) :=
    Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m)
  let original : Fin n → ℂ := fun k ↦ factor (loop k) (loop (k + 1))
  let reversed : Fin n → ℂ := fun k ↦
    factor (surgery k) (surgery (k + 1))
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
      · rw [StatMech.Onsager.ons_revSeg_inside reverse loop (le_refl _) hlm,
          StatMech.Onsager.ons_mir_l hlm,
          StatMech.Onsager.ons_v_m hreverse hboth, hreverse]
      · rw [StatMech.Onsager.ons_revSeg_inside reverse loop hlm (le_refl _),
          StatMech.Onsager.ons_mir_m hlm]
        exact (StatMech.Onsager.ons_v_m hreverse hboth).symm
    · exact StatMech.Onsager.ons_revSeg_outside reverse loop hin
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
  have hsigmaMem : ∀ k ∈ T,
      StatMech.Onsager.ons_mir l m (k + 1) ∈ T := by
    intro k hk
    rw [show T = Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) from rfl,
      Finset.mem_filter] at hk ⊢
    have hk1 : (k + 1 : Fin n).val = k.val + 1 := hadd1 k (by omega)
    have hval : (StatMech.Onsager.ons_mir l m (k + 1)).val =
        l.val + m.val - (k.val + 1) := by
      rw [StatMech.Onsager.ons_mir_val
        (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega), hk1]
    exact ⟨Finset.mem_univ _, by show l.val ≤ _; rw [hval]; omega,
      by show _ < m.val; rw [hval]; omega⟩
  have hsigmaInv : ∀ k ∈ T,
      StatMech.Onsager.ons_mir l m
        (StatMech.Onsager.ons_mir l m (k + 1) + 1) = k := by
    intro k hk
    rw [show T = Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) from rfl,
      Finset.mem_filter] at hk
    have hk1 : (k + 1 : Fin n).val = k.val + 1 := hadd1 k (by omega)
    have hsig : (StatMech.Onsager.ons_mir l m (k + 1)).val =
        l.val + m.val - (k.val + 1) := by
      rw [StatMech.Onsager.ons_mir_val
        (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega), hk1]
    have hsig1 :
        (StatMech.Onsager.ons_mir l m (k + 1) + 1 : Fin n).val =
          l.val + m.val - k.val := by
      rw [hadd1 _ (by rw [hsig]; omega), hsig]
      omega
    apply Fin.ext
    rw [StatMech.Onsager.ons_mir_val
      (by show l.val ≤ _; rw [hsig1]; omega)
      (by show _ ≤ m.val; rw [hsig1]; omega), hsig1]
    omega
  have hreindex :
      (∏ k ∈ T,
        original (StatMech.Onsager.ons_mir l m (k + 1))) =
          ∏ k ∈ T, original k := by
    exact Finset.prod_bij'
      (fun k _ ↦ StatMech.Onsager.ons_mir l m (k + 1))
      (fun k _ ↦ StatMech.Onsager.ons_mir l m (k + 1))
      hsigmaMem hsigmaMem hsigmaInv hsigmaInv (fun k hk ↦ rfl)
  have factor_in : ∀ k ∈ T,
      reversed k =
        original (StatMech.Onsager.ons_mir l m (k + 1)) := by
    intro k hk
    rw [show T = Finset.univ.filter (fun k ↦ l ≤ k ∧ k < m) from rfl,
      Finset.mem_filter] at hk
    have hk1 : (k + 1 : Fin n).val = k.val + 1 := hadd1 k (by omega)
    have hmk : (StatMech.Onsager.ons_mir l m k).val =
        l.val + m.val - k.val :=
      StatMech.Onsager.ons_mir_val hk.2.1 (le_of_lt hk.2.2)
    have hmk1 : (StatMech.Onsager.ons_mir l m (k + 1)).val =
        l.val + m.val - (k.val + 1) := by
      rw [StatMech.Onsager.ons_mir_val
        (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega), hk1]
    have hnext : StatMech.Onsager.ons_mir l m (k + 1) + 1 =
        StatMech.Onsager.ons_mir l m k := by
      apply Fin.ext
      rw [hadd1 _ (by rw [hmk1]; omega), hmk1, hmk]
      omega
    have hsk : surgery k =
        reverse (loop (StatMech.Onsager.ons_mir l m k)) := by
      rw [hs]
      exact StatMech.Onsager.ons_revSeg_inside reverse loop
        hk.2.1 (le_of_lt hk.2.2)
    have hsk1 : surgery (k + 1) =
        reverse (loop (StatMech.Onsager.ons_mir l m (k + 1))) := by
      rw [hs]
      exact StatMech.Onsager.ons_revSeg_inside reverse loop
        (by show l.val ≤ (k + 1).val; rw [hk1]; omega)
        (by show (k + 1).val ≤ m.val; rw [hk1]; omega)
    simp only [reversed, original, hsk, hsk1, hnext]
    exact hfactor _ _
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



theorem kwPrincipalHalfAnglePhase_reverse
    {Dart : Type*} (reverse : Dart → Dart)
    (angle : Dart → Real.Angle)
    (hangle : ∀ dart, angle (reverse dart) = angle dart + (Real.pi : Real.Angle))
    {x y : Dart} (hnonantipodal : angle y - angle x ≠ (Real.pi : Real.Angle)) :
    kwPrincipalHalfAnglePhase angle (reverse y) (reverse x) =
      (kwPrincipalHalfAnglePhase angle x y)⁻¹ := by
  have hdelta : angle (reverse x) - angle (reverse y) =
      -(angle y - angle x) := by
    rw [hangle, hangle]
    abel
  unfold kwPrincipalHalfAnglePhase
  rw [hdelta, Real.Angle.toReal_neg_eq_neg_toReal_iff.mpr hnonantipodal,
    ← Complex.exp_neg]
  congr 1
  push_cast
  ring




theorem kwPrincipalHalfAnglePath_sq
    {Dart : Type*} (reverse : Dart → Dart)
    (angle : Dart → Real.Angle)
    (hangle : ∀ dart, angle (reverse dart) = angle dart + (Real.pi : Real.Angle))
    {N : ℕ} (path : Fin (N + 1) → Dart)
    (hend : path (Fin.last N) = reverse (path 0)) :
    (∏ j : Fin N,
      kwPrincipalHalfAnglePhase angle (path j.castSucc) (path j.succ)) ^ 2 =
        -1 := by
  let Q : ℂ := ∏ j : Fin N,
    kwPrincipalHalfAnglePhase angle (path j.castSucc) (path j.succ)
  let closing : ℂ := kwPrincipalHalfAnglePhase angle
    (path (Fin.last N)) (path 0)
  have hproduct :
      kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) path =
        Q * closing := by
    unfold kwLoopPhaseProduct
    rw [Fin.prod_univ_castSucc]
    congr 1
    · apply Finset.prod_congr rfl
      intro j _
      congr 2
      apply Fin.ext
      simp
    · simp only [Fin.last_add_one, closing]
  have hclosed : (Q * closing) ^ 2 = 1 := by
    rw [← hproduct]
    exact kwLoopPhaseProduct_principal_sq angle path
  have hclosing : closing ^ 2 = -1 := by
    rw [show closing = kwPrincipalHalfAnglePhase angle
      (path (Fin.last N)) (path 0) from rfl,
      kwPrincipalHalfAnglePhase_sq, hend, hangle]
    simp [Complex.exp_mul_I]
  change Q ^ 2 = -1
  calc
    Q ^ 2 = -(Q ^ 2 * closing ^ 2) := by rw [hclosing]; ring
    _ = -(Q * closing) ^ 2 := by ring
    _ = -1 := by rw [hclosed]



theorem kwPrincipalHalfAnglePhase_surgery_sign
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    {n : ℕ} [NeZero n]
    (reverse : Dart → Dart) (hreverse : Function.Involutive reverse)
    (hreverse_ne : ∀ dart, reverse dart ≠ dart)
    (angle : Dart → Real.Angle)
    (hangle : ∀ dart, angle (reverse dart) = angle dart + (Real.pi : Real.Angle))
    (selected : Dart) (loop : Fin n → Dart)
    (hboth : (∃ i, loop i = selected) ∧
      ∃ j, loop j = reverse selected)
    (hnonantipodal : ∀ k : Fin n,
      angle (loop (k + 1)) - angle (loop k) ≠ (Real.pi : Real.Angle)) :
    (∏ k, kwPrincipalHalfAnglePhase angle
        (StatMech.Onsager.ons_surgery selected reverse loop k)
        (StatMech.Onsager.ons_surgery selected reverse loop (k + 1))) =
      -∏ k, kwPrincipalHalfAnglePhase angle (loop k) (loop (k + 1)) := by
  apply kw_phaseProduct_surgery_sign reverse hreverse hreverse_ne
    (kwPrincipalHalfAnglePhase angle) (fun _ _ ↦ True)
    (fun path hend _ ↦ kwPrincipalHalfAnglePath_sq reverse angle hangle path hend)
    selected loop hboth
  · intro k
    trivial
  intro k
  exact kwPrincipalHalfAnglePhase_reverse reverse angle hangle
    (hnonantipodal k)



theorem kwLoopPhaseProduct_involutiveLoopRev
    {Dart : Type*}
    {n : ℕ} [NeZero n]
    (reverse : Dart → Dart) (phase : Dart → Dart → ℂ)
    (loop : Fin n → Dart)
    (hphase : ∀ k : Fin n,
      phase (reverse (loop (k + 1))) (reverse (loop k)) =
        (phase (loop k) (loop (k + 1)))⁻¹)
    (hPsq : kwLoopPhaseProduct phase loop ^ 2 = 1) :
    kwLoopPhaseProduct phase
        (StatMech.Onsager.ons_involutiveLoopRev reverse loop) =
      kwLoopPhaseProduct phase loop := by
  let P := kwLoopPhaseProduct phase loop
  let reflected : Equiv.Perm (Fin n) :=
    (Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n))
  have hterm : ∀ k : Fin n,
      phase (reverse (loop (-k))) (reverse (loop (-(k + 1)))) =
        (phase (loop (-(k + 1))) (loop (-k)))⁻¹ := by
    intro k
    have hnext : (-(k + 1) : Fin n) + 1 = -k := by abel
    simpa only [hnext] using hphase (-(k + 1))
  have hreindex :
      (∏ k : Fin n, phase (loop (-(k + 1))) (loop (-k))) = P := by
    calc
      (∏ k : Fin n, phase (loop (-(k + 1))) (loop (-k))) =
          ∏ k : Fin n, phase
            (loop (reflected k)) (loop (reflected k + 1)) := by
        apply Finset.prod_congr rfl
        intro k _
        congr 2
        change -k = -(k + 1) + 1
        abel
      _ = P := Equiv.prod_comp reflected
        (fun k ↦ phase (loop k) (loop (k + 1)))
  have hPsq' : P ^ 2 = 1 := hPsq
  have hPne : P ≠ 0 := by
    intro hzero
    rw [hzero] at hPsq'
    norm_num at hPsq'
  unfold kwLoopPhaseProduct StatMech.Onsager.ons_involutiveLoopRev
  rw [Finset.prod_congr rfl (fun k _ ↦ hterm k),
    Finset.prod_inv_distrib, hreindex]
  calc
    P⁻¹ = P⁻¹ * 1 := by ring
    _ = P⁻¹ * P ^ 2 := by rw [hPsq']
    _ = (P⁻¹ * P) * P := by rw [pow_two]; ring
    _ = P := by rw [inv_mul_cancel₀ hPne, one_mul]



theorem kwLoopPhaseProduct_principal_involutiveLoopRev
    {Dart : Type*}
    {n : ℕ} [NeZero n]
    (reverse : Dart → Dart) (angle : Dart → Real.Angle)
    (hangle : ∀ dart, angle (reverse dart) = angle dart + (Real.pi : Real.Angle))
    (loop : Fin n → Dart)
    (hnonantipodal : ∀ k : Fin n,
      angle (loop (k + 1)) - angle (loop k) ≠ (Real.pi : Real.Angle)) :
    kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle)
        (StatMech.Onsager.ons_involutiveLoopRev reverse loop) =
      kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) loop := by
  let P := kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) loop
  let reflected : Equiv.Perm (Fin n) :=
    (Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n))
  have hterm : ∀ k : Fin n,
      kwPrincipalHalfAnglePhase angle
          (reverse (loop (-k))) (reverse (loop (-(k + 1)))) =
        (kwPrincipalHalfAnglePhase angle
          (loop (-(k + 1))) (loop (-k)))⁻¹ := by
    intro k
    have hnext : (-(k + 1) : Fin n) + 1 = -k := by abel
    simpa only [hnext] using
      kwPrincipalHalfAnglePhase_reverse reverse angle hangle
        (hnonantipodal (-(k + 1)))
  have hreindex :
      (∏ k : Fin n, kwPrincipalHalfAnglePhase angle
        (loop (-(k + 1))) (loop (-k))) = P := by
    calc
      (∏ k : Fin n, kwPrincipalHalfAnglePhase angle
          (loop (-(k + 1))) (loop (-k))) =
          ∏ k : Fin n, kwPrincipalHalfAnglePhase angle
            (loop (reflected k)) (loop (reflected k + 1)) := by
        apply Finset.prod_congr rfl
        intro k _
        congr 2
        change -k = -(k + 1) + 1
        abel
      _ = P := Equiv.prod_comp reflected
        (fun k ↦ kwPrincipalHalfAnglePhase angle (loop k) (loop (k + 1)))
  have hPsq : P ^ 2 = 1 :=
    kwLoopPhaseProduct_principal_sq angle loop
  have hPne : P ≠ 0 := by
    intro hzero
    rw [hzero] at hPsq
    norm_num at hPsq
  unfold kwLoopPhaseProduct StatMech.Onsager.ons_involutiveLoopRev
  rw [Finset.prod_congr rfl (fun k _ ↦ hterm k),
    Finset.prod_inv_distrib, hreindex]
  calc
    P⁻¹ = P⁻¹ * 1 := by ring
    _ = P⁻¹ * P ^ 2 := by rw [hPsq]
    _ = (P⁻¹ * P) * P := by rw [pow_two]; ring
    _ = P := by rw [inv_mul_cancel₀ hPne, one_mul]



theorem kwGraphLoopScalar_eq_nonbacktracking_mul_phase
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    kwGraphLoopScalar G phase loop =
      (∏ k, kwGraphNonbacktrackingFactor G (loop k) (loop (k + 1))) *
        ∏ k, phase (loop k) (loop (k + 1)) := by
  unfold kwGraphLoopScalar
  rw [Finset.prod_congr rfl (fun k _ ↦ show
    kwGraphTransition G (fun _ ↦ 1) phase (loop k) (loop (k + 1)) =
      kwGraphNonbacktrackingFactor G (loop k) (loop (k + 1)) *
        phase (loop k) (loop (k + 1)) by
      simp only [kwGraphTransition, kwGraphNonbacktrackingFactor,
        SimpleGraph.DartAdj]
      split <;> simp_all)]
  exact Finset.prod_mul_distrib


theorem kwGraphLoopExponent_surgery
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (selected : G.Dart) (loop : Fin n → G.Dart)
    (hboth : (∃ i, loop i = selected) ∧
      ∃ j, loop j = selected.symm) :
    kwGraphLoopExponent G
        (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) =
      kwGraphLoopExponent G loop := by
  unfold kwGraphLoopExponent
  exact StatMech.Onsager.ons_sum_surgery_invariant
    selected SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive
    (fun dart ↦ Finsupp.single dart.edge 1)
    (fun dart ↦ by simp) loop hboth



theorem kwGraphLoopScalar_surgery_sign
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n]
    (phase : G.Dart → G.Dart → ℂ)
    (hpathSq : ∀ {N : ℕ} (path : Fin (N + 1) → G.Dart),
      path (Fin.last N) = (path 0).symm →
        (∀ j : Fin N, G.DartAdj (path j.castSucc) (path j.succ) ∧
          (path j.castSucc).edge ≠ (path j.succ).edge) →
        (∏ j : Fin N, phase (path j.castSucc) (path j.succ)) ^ 2 = -1)
    (hphase : ∀ dart next,
      G.DartAdj dart next → dart.edge ≠ next.edge →
        phase next.symm dart.symm = (phase dart next)⁻¹)
    (selected : G.Dart) (loop : Fin n → G.Dart)
    (hboth : (∃ i, loop i = selected) ∧
      ∃ j, loop j = selected.symm) :
    kwGraphLoopScalar G phase
        (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) =
      -kwGraphLoopScalar G phase loop := by
  let surgery :=
    StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop
  let adjacencyProduct : (Fin n → G.Dart) → ℂ := fun path ↦
    ∏ k, kwGraphNonbacktrackingFactor G (path k) (path (k + 1))
  have hadjacency : adjacencyProduct surgery = adjacencyProduct loop := by
    exact kw_reversibleFactorProduct_surgery
      SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive
      (fun dart ↦ SimpleGraph.Dart.symm_ne dart)
      (kwGraphNonbacktrackingFactor G)
      (kwGraphNonbacktrackingFactor_reverse G) selected loop hboth
  by_cases hzero : adjacencyProduct loop = 0
  · rw [kwGraphLoopScalar_eq_nonbacktracking_mul_phase,
      kwGraphLoopScalar_eq_nonbacktracking_mul_phase]
    change adjacencyProduct surgery * _ = -(adjacencyProduct loop * _)
    rw [hadjacency, hzero]
    ring
  · have hvalid : ∀ k : Fin n,
        G.DartAdj (loop k) (loop (k + 1)) ∧
          (loop k).edge ≠ (loop (k + 1)).edge := by
      intro k
      have hfactor :
          kwGraphNonbacktrackingFactor G (loop k) (loop (k + 1)) ≠ 0 := by
        intro hk
        apply hzero
        apply Finset.prod_eq_zero (Finset.mem_univ k)
        exact hk
      by_contra hstep
      simp [kwGraphNonbacktrackingFactor, hstep] at hfactor
    have hphaseProduct := kw_phaseProduct_surgery_sign
      SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive
      (fun dart ↦ SimpleGraph.Dart.symm_ne dart) phase
      (fun dart next ↦ G.DartAdj dart next ∧ dart.edge ≠ next.edge)
      hpathSq selected loop hboth hvalid
      (fun k ↦ hphase _ _ (hvalid k).1 (hvalid k).2)
    rw [kwGraphLoopScalar_eq_nonbacktracking_mul_phase,
      kwGraphLoopScalar_eq_nonbacktracking_mul_phase]
    change adjacencyProduct surgery * _ = -(adjacencyProduct loop * _)
    rw [hadjacency, hphaseProduct]
    ring



theorem kwGraphLoopWeight_surgery_sign
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n]
    (weight : Sym2 V → ℂ) (phase : G.Dart → G.Dart → ℂ)
    (hpathSq : ∀ {N : ℕ} (path : Fin (N + 1) → G.Dart),
      path (Fin.last N) = (path 0).symm →
        (∀ j : Fin N, G.DartAdj (path j.castSucc) (path j.succ) ∧
          (path j.castSucc).edge ≠ (path j.succ).edge) →
        (∏ j : Fin N, phase (path j.castSucc) (path j.succ)) ^ 2 = -1)
    (hphase : ∀ dart next,
      G.DartAdj dart next → dart.edge ≠ next.edge →
        phase next.symm dart.symm = (phase dart next)⁻¹)
    (selected : G.Dart) (loop : Fin n → G.Dart)
    (hboth : (∃ i, loop i = selected) ∧
      ∃ j, loop j = selected.symm) :
    StatMech.Onsager.ons_loopWeight (kwGraphTransition G weight phase)
        (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) =
      -StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight phase) loop := by
  rw [kwGraphLoopWeight_factor, kwGraphLoopWeight_factor,
    kwGraphLoopExponent_surgery G selected loop hboth,
    kwGraphLoopScalar_surgery_sign G phase hpathSq hphase selected loop hboth]
  ring




theorem kwGraphLoopScalar_principal_surgery_sign
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n]
    (angle : G.Dart → Real.Angle)
    (hangle : ∀ dart, angle dart.symm = angle dart + (Real.pi : Real.Angle))
    (hnonantipodal : ∀ dart next,
      G.DartAdj dart next → dart.edge ≠ next.edge →
        angle next - angle dart ≠ (Real.pi : Real.Angle))
    (selected : G.Dart) (loop : Fin n → G.Dart)
    (hboth : (∃ i, loop i = selected) ∧
      ∃ j, loop j = selected.symm) :
    kwGraphLoopScalar G (kwPrincipalHalfAnglePhase angle)
        (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) =
      -kwGraphLoopScalar G (kwPrincipalHalfAnglePhase angle) loop := by
  let surgery :=
    StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop
  let adjacencyProduct : (Fin n → G.Dart) → ℂ := fun path ↦
    ∏ k, kwGraphNonbacktrackingFactor G (path k) (path (k + 1))
  have hadjacency : adjacencyProduct surgery = adjacencyProduct loop := by
    exact kw_reversibleFactorProduct_surgery
      SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive
      (fun dart ↦ SimpleGraph.Dart.symm_ne dart)
      (kwGraphNonbacktrackingFactor G)
      (kwGraphNonbacktrackingFactor_reverse G) selected loop hboth
  by_cases hzero : adjacencyProduct loop = 0
  · rw [kwGraphLoopScalar_eq_nonbacktracking_mul_phase,
      kwGraphLoopScalar_eq_nonbacktracking_mul_phase]
    change adjacencyProduct surgery * _ = -(adjacencyProduct loop * _)
    rw [hadjacency, hzero]
    ring
  · have hvalid : ∀ k : Fin n,
        G.DartAdj (loop k) (loop (k + 1)) ∧
          (loop k).edge ≠ (loop (k + 1)).edge := by
      intro k
      have hfactor :
          kwGraphNonbacktrackingFactor G (loop k) (loop (k + 1)) ≠ 0 := by
        intro hk
        apply hzero
        apply Finset.prod_eq_zero (Finset.mem_univ k)
        exact hk
      by_contra hstep
      simp [kwGraphNonbacktrackingFactor, hstep] at hfactor
    have hphase := kwPrincipalHalfAnglePhase_surgery_sign
      SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive
      (fun dart ↦ SimpleGraph.Dart.symm_ne dart)
      angle hangle selected loop hboth
      (fun k ↦ hnonantipodal _ _ (hvalid k).1 (hvalid k).2)
    rw [kwGraphLoopScalar_eq_nonbacktracking_mul_phase,
      kwGraphLoopScalar_eq_nonbacktracking_mul_phase]
    change adjacencyProduct surgery * _ = -(adjacencyProduct loop * _)
    rw [hadjacency, hphase]
    ring



theorem kwGraphLoopWeight_principal_surgery_sign
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n]
    (weight : Sym2 V → ℂ) (angle : G.Dart → Real.Angle)
    (hangle : ∀ dart, angle dart.symm = angle dart + (Real.pi : Real.Angle))
    (hnonantipodal : ∀ dart next,
      G.DartAdj dart next → dart.edge ≠ next.edge →
        angle next - angle dart ≠ (Real.pi : Real.Angle))
    (selected : G.Dart) (loop : Fin n → G.Dart)
    (hboth : (∃ i, loop i = selected) ∧
      ∃ j, loop j = selected.symm) :
    StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle))
        (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) =
      -StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) loop := by
  rw [kwGraphLoopWeight_factor, kwGraphLoopWeight_factor,
    kwGraphLoopExponent_surgery G selected loop hboth,
    kwGraphLoopScalar_principal_surgery_sign
      G angle hangle hnonantipodal selected loop hboth]
  ring



theorem kw_principalAngleGraph_fixedOrbitExponent_cancel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n]
    (weight : Sym2 V → ℂ) (angle : G.Dart → Real.Angle)
    (hangle : ∀ dart, angle dart.symm = angle dart + (Real.pi : Real.Angle))
    (hnonantipodal : ∀ dart next,
      G.DartAdj dart next → dart.edge ≠ next.edge →
        angle next - angle dart ≠ (Real.pi : Real.Angle))
    (selected : G.Dart) (exponent : Sym2 G.Dart →₀ ℕ) :
    (∑ loop ∈ kwFixedOrbitExponentLoops (n := n)
        selected SimpleGraph.Dart.symm exponent,
      StatMech.Onsager.ons_loopWeight
        (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle)) loop) = 0 := by
  apply kw_fixedOrbitExponent_surgery_cancel
    (kwGraphTransition G weight (kwPrincipalHalfAnglePhase angle))
    selected SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive
    (SimpleGraph.Dart.symm_ne selected) exponent
  intro loop hloop
  apply kwGraphLoopWeight_principal_surgery_sign
    G weight angle hangle hnonantipodal selected loop
  exact (StatMech.Onsager.ons_mem_loopSetBoth
    selected selected.symm loop).mp hloop

end StatMech.FrontierA
