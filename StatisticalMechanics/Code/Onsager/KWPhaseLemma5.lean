/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.KWLemma5
import Code.Onsager.KWPhaseLoops










namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_dirPhase_spin_opposite (L : ℕ) (a b : Fin 2) (mu : Fin 4) :
    ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) (mu + 2) =
      (ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) mu)⁻¹ := by
  fin_cases mu <;>
    simp [ons_dirPhase]


theorem ons_spinPhase_loopFactor_sq
    {L n : ℕ} [NeZero L] [NeZero n]
    (a b : Fin 2) (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    (∏ k, ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) (d k).2) ^ 2 = 1 := by
  obtain ⟨mx, my, hmx, hmy⟩ := ons_loop_winding_exists d hvalid
  rw [prod_ons_dirPhase _ _ (ons_spinPhase_ne_zero L a)
      (ons_spinPhase_ne_zero L b), hmx, hmy,
    _root_.zpow_mul, _root_.zpow_mul]
  have ha : ons_spinPhase L a ^ (L : ℤ) =
      (-1 : ℂ) ^ (a.val : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L a
  have hb : ons_spinPhase L b ^ (L : ℤ) =
      (-1 : ℂ) ^ (b.val : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L b
  rw [ha, hb]
  have hneg (m : ℤ) : (((-1 : ℂ) ^ m) ^ 2 = 1) := by
    rw [pow_two, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
      show m + m = 2 * m by ring, _root_.zpow_mul]
    norm_num
  rw [← _root_.zpow_mul, ← _root_.zpow_mul, mul_pow,
    hneg, hneg, one_mul]


theorem ons_spinPhase_surgeryFactor
    {L n : ℕ} [NeZero L] [NeZero n] [Fact (2 < L)]
    (a b : Fin 2) (e : ons_Dart L) (d : Fin n → ons_Dart L)
    (hd : d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e))
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    (∏ k, ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b)
        (ons_surgery e (ons_dartRev L) d k).2) =
      ∏ k, ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) (d k).2 := by
  rw [ons_mem_loopSetBoth] at hd
  let rev := ons_dartRev L
  have hrevinv : Function.Involutive rev := ons_dartRev_involutive L
  let l := ons_l e rev d
  let m := ons_m e rev d
  have hlm : l ≤ m := ons_l_le_m hrevinv hd
  have hdm : d m = rev (d l) := ons_v_m hrevinv hd
  have hlm' : l < m := by
    rcases lt_or_eq_of_le hlm with h | h
    · exact h
    · exfalso
      apply ons_dartRev_ne L (d l)
      rw [← show rev = ons_dartRev L from rfl, ← hdm, h]
  let s := ons_surgery e rev d
  have hs : s = ons_revSeg rev l m d := ons_surgery_eq_revSeg hd
  let U : Finset (Fin n) :=
    Finset.univ.filter (fun k => l ≤ k ∧ k ≤ m)
  let phase : Fin 4 → ℂ :=
    ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b)
  let P : ℂ := ∏ k ∈ U, phase (d k).2
  have hlmv : l.val < m.val := hlm'
  have hmn : m.val < n := m.isLt
  have hn2 : 2 ≤ n := by omega
  have hadd1 : ∀ k : Fin n, k.val + 1 < n →
      ((k + 1 : Fin n)).val = k.val + 1 := by
    intro k hk
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : (1 : ℕ) < n),
      Nat.mod_eq_of_lt hk]
  let N := m.val - l.val
  have hidx_bound : ∀ j : Fin (N + 1), l.val + j.val < n := by
    intro j
    have hj := j.isLt
    dsimp [N] at hj
    omega
  let idx : Fin (N + 1) → Fin n := fun j =>
    ⟨l.val + j.val, hidx_bound j⟩
  let w : Fin (N + 1) → ons_Dart L := fun j => d (idx j)
  have hidx_zero : idx 0 = l := by
    apply Fin.ext
    simp [idx]
  have hidx_last : idx (Fin.last N) = m := by
    apply Fin.ext
    simp only [idx, Fin.val_last]
    dsimp [N]
    omega
  have hvalidw : ∀ j : Fin (N + 1),
      (w j).1 = ons_dirStep L (w (j + 1)).2 (w (j + 1)).1 := by
    intro j
    refine Fin.lastCases ?_ (fun q => ?_) j
    · have hwrap : (Fin.last N + 1 : Fin (N + 1)) = 0 := by
        apply Fin.ext
        simp
      rw [hwrap]
      change (d (idx (Fin.last N))).1 =
        ons_dirStep L (d (idx 0)).2 (d (idx 0)).1
      rw [hidx_last, hidx_zero, hdm]
      rfl
    · have hnext : (Fin.castSucc q + 1 : Fin (N + 1)) = q.succ := by
        apply Fin.ext
        simp
      rw [hnext]
      have hstep : idx (Fin.castSucc q) + 1 = idx q.succ := by
        apply Fin.ext
        rw [hadd1]
        · simp only [idx, Fin.val_castSucc, Fin.val_succ]
          omega
        · have hq := q.isLt
          dsimp [N] at hq
          simp only [idx, Fin.val_castSucc]
          omega
      change (d (idx (Fin.castSucc q))).1 =
        ons_dirStep L (d (idx q.succ)).2 (d (idx q.succ)).1
      rw [← hstep]
      exact hvalid (idx (Fin.castSucc q))
  have hwP : (∏ j, phase (w j).2) = P := by
    rw [show P = ∏ k ∈ U, phase (d k).2 from rfl]
    refine Finset.prod_bij (fun j _ => idx j) ?_ ?_ ?_ ?_
    · intro j _
      rw [show U = Finset.univ.filter (fun k => l ≤ k ∧ k ≤ m) from rfl,
        Finset.mem_filter]
      have hj := j.isLt
      dsimp [N] at hj
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · show l.val ≤ (idx j).val
        simp [idx]
      · show (idx j).val ≤ m.val
        simp only [idx]
        omega
    · intro j₁ _ j₂ _ hij
      apply Fin.ext
      have hv := congrArg Fin.val hij
      simp only [idx] at hv
      omega
    · intro k hk
      rw [show U = Finset.univ.filter (fun k => l ≤ k ∧ k ≤ m) from rfl,
        Finset.mem_filter] at hk
      refine ⟨⟨k.val - l.val, ?_⟩, Finset.mem_univ _, ?_⟩
      · dsimp [N]
        omega
      · apply Fin.ext
        simp only [idx]
        omega
    · intro j _
      rfl
  have hP2 : P ^ 2 = 1 := by
    rw [← hwP]
    exact ons_spinPhase_loopFactor_sq a b w hvalidw
  have hmirror : (∏ k ∈ U, phase (d (ons_mir l m k)).2) = P := by
    rw [show P = ∏ k ∈ U, phase (d k).2 from rfl]
    refine Finset.prod_bij'
      (fun k _ => ons_mir l m k) (fun k _ => ons_mir l m k)
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
      change ons_mir l m (ons_mir l m k) = k
      exact ons_mir_mir hk'.1 hk'.2
    · intro k hk
      have hk' : l ≤ k ∧ k ≤ m := by
        simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      change ons_mir l m (ons_mir l m k) = k
      exact ons_mir_mir hk'.1 hk'.2
    · intro k _
      rfl
  have hinside : (∏ k ∈ U, phase (s k).2) = P⁻¹ := by
    calc
      (∏ k ∈ U, phase (s k).2) =
          ∏ k ∈ U, (phase (d (ons_mir l m k)).2)⁻¹ := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [show U = Finset.univ.filter (fun k => l ≤ k ∧ k ≤ m) from rfl,
          Finset.mem_filter] at hk
        have hsk : s k = rev (d (ons_mir l m k)) := by
          rw [hs]
          exact ons_revSeg_inside rev d hk.2.1 hk.2.2
        rw [hsk]
        exact ons_dirPhase_spin_opposite L a b (d (ons_mir l m k)).2
      _ = (∏ k ∈ U, phase (d (ons_mir l m k)).2)⁻¹ := by
        rw [Finset.prod_inv_distrib]
      _ = P⁻¹ := by rw [hmirror]
  have houtside :
      (∏ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k ≤ m)), phase (s k).2) =
        ∏ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k ≤ m)), phase (d k).2 := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [Finset.mem_filter] at hk
    have hsk : s k = d k := by
      rw [hs]
      exact ons_revSeg_outside rev d hk.2
    rw [hsk]
  have hPinv : P⁻¹ = P := by
    exact inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hP2)
  calc
    (∏ k, phase (s k).2) =
        (∏ k ∈ U, phase (s k).2) *
          ∏ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k ≤ m)), phase (s k).2 := by
      rw [show U = Finset.univ.filter (fun k => l ≤ k ∧ k ≤ m) from rfl,
        Finset.prod_filter_mul_prod_filter_not]
    _ = P * ∏ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k ≤ m)),
          phase (d k).2 := by rw [hinside, hPinv, houtside]
    _ = ∏ k, phase (d k).2 := by
      rw [show P = ∏ k ∈ U, phase (d k).2 from rfl,
        show U = Finset.univ.filter (fun k => l ≤ k ∧ k ≤ m) from rfl,
        Finset.prod_filter_mul_prod_filter_not]


theorem ons_KWmatPhase_surgery_sign
    {L n : ℕ} [NeZero L] [NeZero n] [Fact (2 < L)]
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (e : ons_Dart L) (d : Fin n → ons_Dart L)
    (hd : d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
    ons_loopWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        (ons_surgery e (ons_dartRev L) d) =
      -ons_loopWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d := by
  have hsign := ons_KW_surgery_sign x omega homega e d hd
  by_cases hzero : ons_loopWeight (ons_KWmat L x omega) d = 0
  · have hszero : ons_loopWeight (ons_KWmat L x omega)
        (ons_surgery e (ons_dartRev L) d) = 0 := by
      rw [hsign, hzero, neg_zero]
    rw [ons_loopWeight_KWmatPhase, ons_loopWeight_KWmatPhase,
      hzero, hszero]
    ring
  · have hvalid : ∀ k : Fin n,
        (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1 := by
      intro k
      by_contra hk
      apply hzero
      unfold ons_loopWeight
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      simp only [ons_KWmat]
      exact if_neg hk
    have hphase := ons_spinPhase_surgeryFactor a b e d hd hvalid
    rw [ons_loopWeight_KWmatPhase, ons_loopWeight_KWmatPhase,
      hphase, hsign]
    ring


theorem ons_KWmatPhase_mask_surgery_sign
    {L n : ℕ} [NeZero L] [NeZero n] [Fact (2 < L)]
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) (d : Fin n → ons_Dart L)
    (hd : d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
    ons_loopWeight
        (ons_maskMatrix forbidden (ons_KWmatPhase L x omega
          (ons_spinPhase L a) (ons_spinPhase L b)))
        (ons_surgery e (ons_dartRev L) d) =
      -ons_loopWeight
        (ons_maskMatrix forbidden (ons_KWmatPhase L x omega
          (ons_spinPhase L a) (ons_spinPhase L b))) d := by
  have hd' : (∃ i, d i = e) ∧
      (∃ j, d j = ons_dartRev L e) := by
    simpa only [ons_mem_loopSetBoth] using hd
  have hhit := ons_surgery_hits_iff forbidden hforbidden hd'
  rw [ons_loopWeight_maskMatrix, ons_loopWeight_maskMatrix]
  by_cases h : ∃ k, d k ∈ forbidden
  · rw [if_pos h, if_pos (hhit.mpr h)]
    simp
  · rw [if_neg h, if_neg (fun hs => h (hhit.mp hs))]
    exact ons_KWmatPhase_surgery_sign x omega homega a b e d hd


theorem ons_KWmatPhase_lemma5
    {L n : ℕ} [NeZero L] [NeZero n] [Fact (2 < L)]
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (e : ons_Dart L) :
    ∑ d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e),
      ons_loopWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d = 0 := by
  apply ons_lemma5 _ e (ons_dartRev L)
    (ons_dartRev_involutive L) (ons_dartRev_ne L e)
  intro d hd
  exact ons_KWmatPhase_surgery_sign x omega homega a b e d hd

theorem ons_KWmatPhase_mask_lemma5
    {L n : ℕ} [NeZero L] [NeZero n] [Fact (2 < L)]
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    ∑ d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e),
      ons_loopWeight
        (ons_maskMatrix forbidden (ons_KWmatPhase L x omega
          (ons_spinPhase L a) (ons_spinPhase L b))) d = 0 := by
  apply ons_lemma5 _ e (ons_dartRev L)
    (ons_dartRev_involutive L) (ons_dartRev_ne L e)
  intro d hd
  exact ons_KWmatPhase_mask_surgery_sign
    x omega homega a b forbidden hforbidden e d hd


theorem ons_loopSum_spinPhase_both_zero
    {L : ℕ} [NeZero L] [Fact (2 < L)]
    (n : ℕ) (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (e : ons_Dart L) :
    (∑ d ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter
        (fun d => (∃ i, d i = e) ∧ (∃ j, d j = ons_dartRev L e)),
      ons_loopWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d) = 0 := by
  have hset :
      ((Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter
        (fun d => (∃ i, d i = e) ∧ (∃ j, d j = ons_dartRev L e))) =
        ons_loopSetBoth (n := n + 1) e (ons_dartRev L e) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ons_mem_loopSetBoth]
  rw [hset]
  exact ons_KWmatPhase_lemma5 x omega homega a b e

theorem ons_loopSum_spinPhase_mask_both_zero
    {L : ℕ} [NeZero L] [Fact (2 < L)]
    (n : ℕ) (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    (∑ d ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter
        (fun d => (∃ i, d i = e) ∧ (∃ j, d j = ons_dartRev L e)),
      ons_loopWeight
        (ons_maskMatrix forbidden (ons_KWmatPhase L x omega
          (ons_spinPhase L a) (ons_spinPhase L b))) d) = 0 := by
  have hset :
      ((Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter
        (fun d => (∃ i, d i = e) ∧ (∃ j, d j = ons_dartRev L e))) =
        ons_loopSetBoth (n := n + 1) e (ons_dartRev L e) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ons_mem_loopSetBoth]
  rw [hset]
  exact ons_KWmatPhase_mask_lemma5
    x omega homega a b forbidden hforbidden e

end StatMech.Onsager
