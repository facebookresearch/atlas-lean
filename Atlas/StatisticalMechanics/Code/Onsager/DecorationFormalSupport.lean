/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationFormalCoefficient










namespace StatMech.Onsager

open BigOperators Finset

theorem ons_sum_surgery_invariant
    {E M : Type*} [Fintype E] [DecidableEq E] [AddCommMonoid M]
    {n : ℕ} [NeZero n] (e : E) (rev : E → E)
    (hrev : Function.Involutive rev) (f : E → M)
    (hf : ∀ x, f (rev x) = f x) (loop : Fin n → E)
    (hloop : (∃ i, loop i = e) ∧ (∃ j, loop j = rev e)) :
    (∑ k, f (ons_surgery e rev loop k)) = ∑ k, f (loop k) := by
  let l := ons_l e rev loop
  let m := ons_m e rev loop
  have hlm : l ≤ m := ons_l_le_m hrev hloop
  let surgery := ons_surgery e rev loop
  have hs : surgery = ons_revSeg rev l m loop := ons_surgery_eq_revSeg hloop
  let U : Finset (Fin n) :=
    Finset.univ.filter (fun k => l ≤ k ∧ k ≤ m)
  let insideSum : M := ∑ k ∈ U, f (loop k)
  have hmirror : (∑ k ∈ U, f (loop (ons_mir l m k))) = insideSum := by
    rw [show insideSum = ∑ k ∈ U, f (loop k) from rfl]
    refine Finset.sum_bij'
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
      exact ons_mir_mir hk'.1 hk'.2
    · intro k hk
      have hk' : l ≤ k ∧ k ≤ m := by
        simpa only [U, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      exact ons_mir_mir hk'.1 hk'.2
    · intro k _
      rfl
  have hinside : (∑ k ∈ U, f (surgery k)) = insideSum := by
    calc
      (∑ k ∈ U, f (surgery k)) =
          ∑ k ∈ U, f (loop (ons_mir l m k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [show U = Finset.univ.filter (fun k => l ≤ k ∧ k ≤ m) from rfl,
          Finset.mem_filter] at hk
        have hsk : surgery k = rev (loop (ons_mir l m k)) := by
          rw [hs]
          exact ons_revSeg_inside rev loop hk.2.1 hk.2.2
        rw [hsk, hf]
      _ = insideSum := hmirror
  have houtside :
      (∑ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k ≤ m)), f (surgery k)) =
        ∑ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k ≤ m)), f (loop k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_filter] at hk
    have hsk : surgery k = loop k := by
      rw [hs]
      exact ons_revSeg_outside rev loop hk.2
    rw [hsk]
  calc
    (∑ k, f (surgery k)) =
        (∑ k ∈ U, f (surgery k)) +
          ∑ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k ≤ m)),
            f (surgery k) := by
      rw [show U = Finset.univ.filter (fun k => l ≤ k ∧ k ≤ m) from rfl,
        Finset.sum_filter_add_sum_filter_not]
    _ = insideSum +
          ∑ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k ≤ m)),
            f (loop k) := by rw [hinside, houtside]
    _ = ∑ k, f (loop k) := by
      rw [show insideSum = ∑ k ∈ U, f (loop k) from rfl,
        show U = Finset.univ.filter (fun k => l ≤ k ∧ k ≤ m) from rfl,
        Finset.sum_filter_add_sum_filter_not]

theorem ons_decLoopExternalExponent_surgery
    (L : ℕ) [NeZero L] {n : ℕ} [NeZero n] (d : ons_Dart L)
    (loop : Fin n → ons_Dart L)
    (hloop : (∃ i, loop i = d) ∧
      (∃ j, loop j = ons_dartRev L d)) :
    ons_decLoopExternalExponent L
        (ons_surgery d (ons_dartRev L) loop) =
      ons_decLoopExternalExponent L loop := by
  unfold ons_decLoopExternalExponent
  exact ons_sum_surgery_invariant d (ons_dartRev L)
    (ons_dartRev_involutive L)
    (fun e => Finsupp.single s(e, ons_dartRev L e) 1)
    (fun e => by
      change Finsupp.single
        s(ons_dartRev L e, ons_dartRev L (ons_dartRev L e)) 1 =
          Finsupp.single s(e, ons_dartRev L e) 1
      rw [ons_dartRev_involutive, Sym2.eq_swap])
    loop hloop

theorem ons_decLoopInternalExponent_surgery
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : ons_Dart L) (loop : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (loop k).1 =
        ons_dirStep L (loop (k + 1)).2 (loop (k + 1)).1)
    (hloop : (∃ i, loop i = d) ∧
      (∃ j, loop j = ons_dartRev L d)) :
    ons_decLoopInternalExponent L
        (ons_surgery d (ons_dartRev L) loop) =
      ons_decLoopInternalExponent L loop := by
  classical
  let rev := ons_dartRev L
  have hrevinv : Function.Involutive rev := ons_dartRev_involutive L
  let l := ons_l d rev loop
  let m := ons_m d rev loop
  have hlm : l ≤ m := ons_l_le_m hrevinv hloop
  have hvm : loop m = rev (loop l) := ons_v_m hrevinv hloop
  have hlm' : l < m := by
    rcases lt_or_eq_of_le hlm with hlt | heq
    · exact hlt
    · exfalso
      apply ons_dartRev_ne L (loop l)
      rw [← show rev = ons_dartRev L from rfl, ← hvm, heq]
  let surgery := ons_surgery d rev loop
  have hs : surgery = ons_revSeg rev l m loop :=
    ons_surgery_eq_revSeg hloop
  let term : (Fin n → ons_Dart L) → Fin n → ons_DecEdge L →₀ ℕ :=
    fun v k => ∑ i ∈ ons_decChainPathIndices
        ((v (k + 1)).2 + 2) (v k).2,
      Finsupp.single (ons_decChainEdge (v k).1 i) 1
  change (∑ k, term surgery k) = ∑ k, term loop k
  have hadd1 : ∀ k : Fin n, k.val + 1 < n →
      ((k + 1 : Fin n)).val = k.val + 1 := by
    intro k hk
    rw [Fin.val_add, Fin.val_one',
      Nat.mod_eq_of_lt (by omega : (1 : ℕ) < n),
      Nat.mod_eq_of_lt hk]
  have soff : ∀ p : Fin n, ¬(l < p ∧ p < m) →
      surgery p = loop p := by
    intro p hp
    rw [hs]
    by_cases hin : l ≤ p ∧ p ≤ m
    · obtain ⟨hlp, hpm⟩ := hin
      have hple : p = l ∨ p = m := by
        by_contra hc
        rw [not_or] at hc
        exact hp ⟨lt_of_le_of_ne hlp (Ne.symm hc.1),
          lt_of_le_of_ne hpm hc.2⟩
      rcases hple with rfl | rfl
      · rw [ons_revSeg_inside rev loop (le_refl _) hlm,
          ons_mir_l hlm, hvm, hrevinv]
      · rw [ons_revSeg_inside rev loop hlm (le_refl _),
          ons_mir_m hlm]
        exact hvm.symm
    · exact ons_revSeg_outside rev loop hin
  have term_off : ∀ k : Fin n, ¬(l ≤ k ∧ k < m) →
      term surgery k = term loop k := by
    intro k hk
    have hk0 : surgery k = loop k := by
      apply soff
      rintro ⟨hlk, hkm⟩
      exact hk ⟨le_of_lt hlk, hkm⟩
    have hk1 : surgery (k + 1) = loop (k + 1) := by
      apply soff
      rintro ⟨hlk1, hk1m⟩
      apply hk
      by_cases hkn : k.val + 1 < n
      · have hval : (k + 1 : Fin n).val = k.val + 1 := hadd1 k hkn
        have hlv : l.val < (k + 1 : Fin n).val := hlk1
        have hmv : (k + 1 : Fin n).val < m.val := hk1m
        rw [hval] at hlv hmv
        exact ⟨by show l.val ≤ k.val; omega,
          by show k.val < m.val; omega⟩
      · exfalso
        have hkn' : k.val + 1 = n := by
          have := k.isLt
          omega
        have hval0 : (k + 1 : Fin n).val = 0 := by
          rw [Fin.val_add, Fin.val_one',
            Nat.mod_eq_of_lt (by omega : (1 : ℕ) < n),
            hkn', Nat.mod_self]
        have hlv : l.val < (k + 1 : Fin n).val := hlk1
        rw [hval0] at hlv
        omega
    simp only [term, hk0, hk1]
  let T : Finset (Fin n) :=
    Finset.univ.filter (fun k => l ≤ k ∧ k < m)
  have hsigmaMem : ∀ k ∈ T, ons_mir l m (k + 1) ∈ T := by
    intro k hk
    rw [show T = Finset.univ.filter
      (fun k => l ≤ k ∧ k < m) from rfl,
      Finset.mem_filter] at hk ⊢
    obtain ⟨-, hlk, hkm⟩ := hk
    have hk1 : (k + 1 : Fin n).val = k.val + 1 :=
      hadd1 k (by omega)
    have hlk1 : l ≤ (k + 1 : Fin n) := by
      show l.val ≤ _
      rw [hk1]
      omega
    have hk1m : (k + 1 : Fin n) ≤ m := by
      show _ ≤ m.val
      rw [hk1]
      omega
    have hval : (ons_mir l m (k + 1)).val =
        l.val + m.val - (k.val + 1) := by
      rw [ons_mir_val hlk1 hk1m, hk1]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · show l.val ≤ _
      rw [hval]
      omega
    · show _ < m.val
      rw [hval]
      omega
  have hsigmaSigma : ∀ k ∈ T,
      ons_mir l m (ons_mir l m (k + 1) + 1) = k := by
    intro k hk
    rw [show T = Finset.univ.filter
      (fun k => l ≤ k ∧ k < m) from rfl,
      Finset.mem_filter] at hk
    obtain ⟨-, hlk, hkm⟩ := hk
    have hk1 : (k + 1 : Fin n).val = k.val + 1 :=
      hadd1 k (by omega)
    have hlk1 : l ≤ (k + 1 : Fin n) := by
      show l.val ≤ _
      rw [hk1]
      omega
    have hk1m : (k + 1 : Fin n) ≤ m := by
      show _ ≤ m.val
      rw [hk1]
      omega
    have hmir : (ons_mir l m (k + 1)).val =
        l.val + m.val - (k.val + 1) := by
      rw [ons_mir_val hlk1 hk1m, hk1]
    have hmir1 : (ons_mir l m (k + 1) + 1 : Fin n).val =
        l.val + m.val - k.val := by
      rw [hadd1 _ (by rw [hmir]; omega), hmir]
      omega
    have hlmir : l ≤ (ons_mir l m (k + 1) + 1 : Fin n) := by
      show l.val ≤ _
      rw [hmir1]
      omega
    have hmirm : (ons_mir l m (k + 1) + 1 : Fin n) ≤ m := by
      show _ ≤ m.val
      rw [hmir1]
      omega
    apply Fin.ext
    rw [ons_mir_val hlmir hmirm, hmir1]
    omega
  have hsigmaReindex :
      (∑ k ∈ T, term loop (ons_mir l m (k + 1))) =
        ∑ k ∈ T, term loop k := by
    exact Finset.sum_bij'
      (fun k _ => ons_mir l m (k + 1))
      (fun k _ => ons_mir l m (k + 1))
      hsigmaMem hsigmaMem hsigmaSigma hsigmaSigma (fun k _ => rfl)
  have term_in : ∀ k ∈ T,
      term surgery k = term loop (ons_mir l m (k + 1)) := by
    intro k hk
    rw [show T = Finset.univ.filter
      (fun k => l ≤ k ∧ k < m) from rfl,
      Finset.mem_filter] at hk
    obtain ⟨-, hlk, hkm⟩ := hk
    have hkm' : k ≤ m := le_of_lt hkm
    have hk1 : (k + 1 : Fin n).val = k.val + 1 :=
      hadd1 k (by omega)
    have hlk1 : l ≤ (k + 1 : Fin n) := by
      show l.val ≤ _
      rw [hk1]
      omega
    have hk1m : (k + 1 : Fin n) ≤ m := by
      show _ ≤ m.val
      rw [hk1]
      omega
    have hmirk : (ons_mir l m k).val =
        l.val + m.val - k.val := ons_mir_val hlk hkm'
    have hsigk : (ons_mir l m (k + 1)).val =
        l.val + m.val - (k.val + 1) := by
      rw [ons_mir_val hlk1 hk1m, hk1]
    have hsig1 :
        (ons_mir l m (k + 1) + 1 : Fin n) = ons_mir l m k := by
      apply Fin.ext
      rw [hadd1 _ (by rw [hsigk]; omega), hsigk, hmirk]
      omega
    have hsk : surgery k = rev (loop (ons_mir l m k)) := by
      rw [hs]
      exact ons_revSeg_inside rev loop hlk hkm'
    have hsk1 : surgery (k + 1) =
        rev (loop (ons_mir l m (k + 1))) := by
      rw [hs]
      exact ons_revSeg_inside rev loop hlk1 hk1m
    have hv := hvalid (ons_mir l m (k + 1))
    rw [hsig1] at hv
    simp only [term, hsk, hsk1, rev, ons_dartRev, add_assoc]
    rw [hsig1, show (2 + 2 : Fin 4) = 0 by decide, add_zero,
      ← hv, ons_decChainPathIndices_comm]
  have hinside : (∑ k ∈ T, term surgery k) =
      ∑ k ∈ T, term loop k := by
    calc
      (∑ k ∈ T, term surgery k) =
          ∑ k ∈ T, term loop (ons_mir l m (k + 1)) := by
        apply Finset.sum_congr rfl
        exact term_in
      _ = ∑ k ∈ T, term loop k := hsigmaReindex
  have houtside :
      (∑ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k < m)),
          term surgery k) =
        ∑ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k < m)),
          term loop k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_filter] at hk
    exact term_off k hk.2
  calc
    (∑ k, term surgery k) =
        (∑ k ∈ T, term surgery k) +
          ∑ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k < m)),
            term surgery k := by
      rw [show T = Finset.univ.filter
        (fun k => l ≤ k ∧ k < m) from rfl,
        Finset.sum_filter_add_sum_filter_not]
    _ = (∑ k ∈ T, term loop k) +
          ∑ k ∈ Finset.univ.filter (fun k => ¬(l ≤ k ∧ k < m)),
            term loop k := by rw [hinside, houtside]
    _ = ∑ k, term loop k := by
      rw [show T = Finset.univ.filter
        (fun k => l ≤ k ∧ k < m) from rfl,
        Finset.sum_filter_add_sum_filter_not]

theorem ons_decLoopExponent_surgery
    (L : ℕ) [NeZero L] [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : ons_Dart L) (loop : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (loop k).1 =
        ons_dirStep L (loop (k + 1)).2 (loop (k + 1)).1)
    (hloop : (∃ i, loop i = d) ∧
      (∃ j, loop j = ons_dartRev L d)) :
    ons_decLoopExponent L
        (ons_surgery d (ons_dartRev L) loop) =
      ons_decLoopExponent L loop := by
  rw [ons_decLoopExponent_eq_external_add_internal,
    ons_decLoopExponent_eq_external_add_internal,
    ons_decLoopExternalExponent_surgery L d loop hloop,
    ons_decLoopInternalExponent_surgery L d loop hvalid hloop]

theorem ons_decLoopScalar_surgery_sign
    (L : ℕ) [NeZero L] [Fact (2 < L)] {n : ℕ} [NeZero n]
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (d : ons_Dart L)
    (loop : Fin n → ons_Dart L)
    (hloop : (∃ i, loop i = d) ∧
      (∃ j, loop j = ons_dartRev L d)) :
    ons_decLoopScalar L omega
        (ons_spinPhase L a) (ons_spinPhase L b)
        (ons_surgery d (ons_dartRev L) loop) =
      -ons_decLoopScalar L omega
        (ons_spinPhase L a) (ons_spinPhase L b) loop := by
  have hmem : loop ∈
      ons_loopSetBoth (n := n) d (ons_dartRev L d) := by
    simpa only [ons_mem_loopSetBoth] using hloop
  rw [ons_decLoopScalar_eq_loopWeight_one,
    ons_decLoopScalar_eq_loopWeight_one]
  exact ons_KWmatWeightedPhase_surgery_sign
    (fun _ => 1) omega homega a b d loop hmem

theorem ons_KWmatDecorationWeightedPhase_surgery_sign
    (L : ℕ) [NeZero L] [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (d : ons_Dart L)
    (loop : Fin n → ons_Dart L)
    (hloop : (∃ i, loop i = d) ∧
      (∃ j, loop j = ons_dartRev L d)) :
    ons_loopWeight
        (ons_KWmatDecorationWeightedPhase L decWeight omega
          (ons_spinPhase L a) (ons_spinPhase L b))
        (ons_surgery d (ons_dartRev L) loop) =
      -ons_loopWeight
        (ons_KWmatDecorationWeightedPhase L decWeight omega
          (ons_spinPhase L a) (ons_spinPhase L b)) loop := by
  have hscalarSign :
      ons_decLoopScalar L omega
          (ons_spinPhase L a) (ons_spinPhase L b)
          (ons_surgery d (ons_dartRev L) loop) =
        -ons_decLoopScalar L omega
          (ons_spinPhase L a) (ons_spinPhase L b) loop := by
    exact ons_decLoopScalar_surgery_sign
      L omega homega a b d loop hloop
  rw [ons_loopWeight_KWmatDecorationWeightedPhase,
    ons_loopWeight_KWmatDecorationWeightedPhase]
  by_cases hscalar : ons_decLoopScalar L omega
      (ons_spinPhase L a) (ons_spinPhase L b) loop = 0
  · rw [hscalarSign, hscalar, neg_zero, zero_mul, zero_mul, neg_zero]
  · have hvalid := ons_decLoop_valid_of_scalar_ne_zero
      L omega (ons_spinPhase L a) (ons_spinPhase L b) loop hscalar
    rw [hscalarSign,
      ons_decLoopExponent_surgery L d loop hvalid hloop]
    ring

theorem ons_KWmatDecorationWeightedPhase_lemma5
    (L : ℕ) [NeZero L] [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (d : ons_Dart L) :
    ∑ loop ∈ ons_loopSetBoth (n := n) d (ons_dartRev L d),
      ons_loopWeight
        (ons_KWmatDecorationWeightedPhase L decWeight omega
          (ons_spinPhase L a) (ons_spinPhase L b)) loop = 0 := by
  apply ons_lemma5 _ d (ons_dartRev L)
    (ons_dartRev_involutive L) (ons_dartRev_ne L d)
  intro loop hloop
  apply ons_KWmatDecorationWeightedPhase_surgery_sign
    L decWeight omega homega a b d loop
  simpa only [ons_mem_loopSetBoth] using hloop

theorem ons_KWmatDecorationWeightedPhase_mask_surgery_sign
    (L : ℕ) [NeZero L] [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) (loop : Fin n → ons_Dart L)
    (hloop : loop ∈
      ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
    ons_loopWeight
        (ons_maskMatrix forbidden
          (ons_KWmatDecorationWeightedPhase L decWeight omega
            (ons_spinPhase L a) (ons_spinPhase L b)))
        (ons_surgery e (ons_dartRev L) loop) =
      -ons_loopWeight
        (ons_maskMatrix forbidden
          (ons_KWmatDecorationWeightedPhase L decWeight omega
            (ons_spinPhase L a) (ons_spinPhase L b))) loop := by
  have hloop' : (∃ i, loop i = e) ∧
      (∃ j, loop j = ons_dartRev L e) := by
    simpa only [ons_mem_loopSetBoth] using hloop
  have hhit := ons_surgery_hits_iff forbidden hforbidden hloop'
  rw [ons_loopWeight_maskMatrix, ons_loopWeight_maskMatrix]
  by_cases h : ∃ k, loop k ∈ forbidden
  · rw [if_pos h, if_pos (hhit.mpr h)]
    simp
  · rw [if_neg h, if_neg (fun hs => h (hhit.mp hs))]
    exact ons_KWmatDecorationWeightedPhase_surgery_sign
      L decWeight omega homega a b e loop hloop'

theorem ons_KWmatDecorationWeightedPhase_mask_lemma5
    (L : ℕ) [NeZero L] [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    ∑ loop ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e),
      ons_loopWeight
        (ons_maskMatrix forbidden
          (ons_KWmatDecorationWeightedPhase L decWeight omega
            (ons_spinPhase L a) (ons_spinPhase L b))) loop = 0 := by
  apply ons_lemma5 _ e (ons_dartRev L)
    (ons_dartRev_involutive L) (ons_dartRev_ne L e)
  exact ons_KWmatDecorationWeightedPhase_mask_surgery_sign
    L decWeight omega homega a b forbidden hforbidden e

theorem ons_loopWeight_KWmatDecorationWeightedPhase_loopRev
    (L : ℕ) [NeZero L] [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (loop : Fin n → ons_Dart L) :
    ons_loopWeight
        (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        (ons_loopRev L loop) =
      ons_loopWeight
        (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) loop := by
  rw [ons_loopWeight_KWmatDecorationWeightedPhase,
    ons_loopWeight_KWmatDecorationWeightedPhase]
  have hscalar := ons_decLoopScalar_loopRev_spin L a b loop
  by_cases hzero : ons_decLoopScalar L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) loop = 0
  · rw [hscalar, hzero, zero_mul, zero_mul]
  · have hvalid := ons_decLoop_valid_of_scalar_ne_zero
      L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) loop hzero
    rw [hscalar, ons_decLoopExponent_loopRev L loop hvalid]

theorem ons_loopWeight_KWmatDecorationWeightedPhase_mask_loopRev
    (L : ℕ) [NeZero L] [Fact (2 < L)] {n : ℕ} [NeZero n]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (loop : Fin n → ons_Dart L) :
    ons_loopWeight
        (ons_maskMatrix forbidden
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b)))
        (ons_loopRev L loop) =
      ons_loopWeight
        (ons_maskMatrix forbidden
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) loop := by
  have hhit := ons_loopRev_hits_iff forbidden hforbidden loop
  rw [ons_loopWeight_maskMatrix, ons_loopWeight_maskMatrix]
  by_cases h : ∃ k, loop k ∈ forbidden
  · rw [if_pos h, if_pos (hhit.mpr h)]
  · rw [if_neg h, if_neg (fun hr => h (hhit.mp hr))]
    exact ons_loopWeight_KWmatDecorationWeightedPhase_loopRev
      L decWeight a b loop

theorem ons_externalDecoratedEdge_eq_iff
    (L : ℕ) (d e : ons_Dart L) :
    s(e, ons_dartRev L e) = s(d, ons_dartRev L d) ↔
      e = d ∨ e = ons_dartRev L d := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (⟨hed, hrev⟩ | ⟨herev, hde⟩)
    · exact Or.inl hed
    · exact Or.inr herev
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, ons_dartRev_involutive L d⟩

theorem ons_decChainEdge_eq_iff
    {L : ℕ} (site site' : ZMod L × ZMod L) (i j : Fin 3) :
    ons_decChainEdge site i = ons_decChainEdge site' j ↔
      site = site' ∧ i = j := by
  constructor
  · intro h
    simp only [ons_decChainEdge, Sym2.eq_iff, Prod.mk.injEq,
      Fin.ext_iff] at h
    rcases h with h | h
    · exact ⟨h.1.1, Fin.ext h.1.2⟩
    · have hij : i.val = j.val + 1 ∧ i.val + 1 = j.val :=
        ⟨h.1.2, h.2.2⟩
      omega
  · rintro ⟨rfl, rfl⟩
    rfl

theorem ons_decLoopInternalExponent_chain_apply
    (L : ℕ) {n : ℕ} [NeZero n]
    (loop : Fin n → ons_Dart L)
    (site : ZMod L × ZMod L) (i : Fin 3) :
    ons_decLoopInternalExponent L loop (ons_decChainEdge site i) =
      ∑ k, if (loop k).1 = site ∧
          i ∈ ons_decChainPathIndices
            ((loop (k + 1)).2 + 2) (loop k).2 then 1 else 0 := by
  classical
  unfold ons_decLoopInternalExponent
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finsupp.finsetSum_apply]
  by_cases hsite : (loop k).1 = site
  · subst site
    by_cases hi : i ∈ ons_decChainPathIndices
        ((loop (k + 1)).2 + 2) (loop k).2
    · rw [if_pos ⟨rfl, hi⟩]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        rw [Finsupp.single_apply, if_neg]
        intro hedge
        exact hji (ons_decChainEdge_injective (loop k).1 hedge)
      · exact fun hnot => (hnot hi).elim
    · rw [if_neg (fun h => hi h.2)]
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finsupp.single_apply, if_neg]
      intro hedge
      have hji := ons_decChainEdge_injective (loop k).1 hedge
      subst j
      exact hi hj
  · rw [if_neg (fun h => hsite h.1)]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finsupp.single_apply, if_neg]
    intro hedge
    exact hsite (ons_decChainEdge_eq_iff
      (loop k).1 site j i |>.mp hedge).1

theorem ons_decLoopExternalExponent_chain_apply
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (loop : Fin n → ons_Dart L)
    (site : ZMod L × ZMod L) (i : Fin 3) :
    ons_decLoopExternalExponent L loop (ons_decChainEdge site i) = 0 := by
  classical
  unfold ons_decLoopExternalExponent
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finsupp.single_apply, if_neg]
  intro hedge
  apply ons_decChainEdge_not_external L site i
  exact ⟨loop k, hedge.symm⟩

theorem ons_decLoopExponent_chain_apply
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (loop : Fin n → ons_Dart L)
    (site : ZMod L × ZMod L) (i : Fin 3) :
    ons_decLoopExponent L loop (ons_decChainEdge site i) =
      ∑ k, if (loop k).1 = site ∧
          i ∈ ons_decChainPathIndices
            ((loop (k + 1)).2 + 2) (loop k).2 then 1 else 0 := by
  rw [ons_decLoopExponent_eq_external_add_internal,
    Finsupp.add_apply, ons_decLoopExternalExponent_chain_apply,
    ons_decLoopInternalExponent_chain_apply, zero_add]

theorem ons_decLoopExponent_chain_apply_eq_card
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (loop : Fin n → ons_Dart L)
    (site : ZMod L × ZMod L) (i : Fin 3) :
    ons_decLoopExponent L loop (ons_decChainEdge site i) =
      (Finset.univ.filter fun k => (loop k).1 = site ∧
        i ∈ ons_decChainPathIndices
          ((loop (k + 1)).2 + 2) (loop k).2).card := by
  rw [ons_decLoopExponent_chain_apply]
  symm
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem ons_two_le_decLoopExponent_chain_iff
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (loop : Fin n → ons_Dart L)
    (site : ZMod L × ZMod L) (i : Fin 3) :
    2 ≤ ons_decLoopExponent L loop (ons_decChainEdge site i) ↔
      ∃ k j : Fin n, k ≠ j ∧
        (loop k).1 = site ∧
        i ∈ ons_decChainPathIndices
          ((loop (k + 1)).2 + 2) (loop k).2 ∧
        (loop j).1 = site ∧
        i ∈ ons_decChainPathIndices
          ((loop (j + 1)).2 + 2) (loop j).2 := by
  rw [ons_decLoopExponent_chain_apply_eq_card]
  constructor
  · intro hcard
    have hone : 1 < (Finset.univ.filter fun k => (loop k).1 = site ∧
        i ∈ ons_decChainPathIndices
          ((loop (k + 1)).2 + 2) (loop k).2).card := by omega
    obtain ⟨k, hk, j, hj, hkj⟩ := Finset.one_lt_card.mp hone
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hj
    exact ⟨k, j, hkj, hk.1, hk.2, hj.1, hj.2⟩
  · rintro ⟨k, j, hkj, hksite, hki, hjsite, hji⟩
    have hone : 1 < (Finset.univ.filter fun k => (loop k).1 = site ∧
        i ∈ ons_decChainPathIndices
          ((loop (k + 1)).2 + 2) (loop k).2).card := by
      rw [Finset.one_lt_card]
      exact ⟨k, by simp [hksite, hki], j, by simp [hjsite, hji], hkj⟩
    omega

theorem ons_decLoopInternalExponent_external_apply
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (loop : Fin n → ons_Dart L) (d : ons_Dart L) :
    ons_decLoopInternalExponent L loop
        s(d, ons_dartRev L d) = 0 := by
  classical
  unfold ons_decLoopInternalExponent
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finsupp.single_apply, if_neg]
  intro heq
  apply ons_decChainEdge_not_external L (loop k).1 i
  exact ⟨d, heq⟩

theorem ons_decLoopExternalExponent_external_apply
    (L : ℕ) {n : ℕ} [NeZero n]
    (loop : Fin n → ons_Dart L) (d : ons_Dart L) :
    ons_decLoopExternalExponent L loop s(d, ons_dartRev L d) =
      ∑ k, if loop k = d ∨ loop k = ons_dartRev L d then 1 else 0 := by
  classical
  unfold ons_decLoopExternalExponent
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finsupp.single_apply]
  exact if_congr (ons_externalDecoratedEdge_eq_iff L d (loop k)) rfl rfl

theorem ons_decLoopExponent_external_apply
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (loop : Fin n → ons_Dart L) (d : ons_Dart L) :
    ons_decLoopExponent L loop s(d, ons_dartRev L d) =
      ∑ k, if loop k = d ∨ loop k = ons_dartRev L d then 1 else 0 := by
  rw [ons_decLoopExponent_eq_external_add_internal,
    Finsupp.add_apply,
    ons_decLoopExternalExponent_external_apply,
    ons_decLoopInternalExponent_external_apply, add_zero]

theorem ons_decLoopExponent_external_pos_iff
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (loop : Fin n → ons_Dart L) (d : ons_Dart L) :
    0 < ons_decLoopExponent L loop s(d, ons_dartRev L d) ↔
      (∃ k, loop k = d) ∨ ∃ k, loop k = ons_dartRev L d := by
  rw [ons_decLoopExponent_external_apply]
  constructor
  · intro hpos
    by_contra hnone
    push Not at hnone
    have hzero :
        (∑ k, if loop k = d ∨ loop k = ons_dartRev L d then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg]
      exact not_or_intro (hnone.1 k) (hnone.2 k)
    omega
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · have hone :
          (if loop k = d ∨ loop k = ons_dartRev L d then 1 else 0) = 1 := by
        rw [if_pos (Or.inl hk)]
      have hle : 1 ≤
          ∑ j, if loop j = d ∨ loop j = ons_dartRev L d then 1 else 0 := by
        calc
          1 = if loop k = d ∨ loop k = ons_dartRev L d then 1 else 0 := hone.symm
          _ ≤ ∑ j, if loop j = d ∨ loop j = ons_dartRev L d then 1 else 0 :=
            Finset.single_le_sum
              (fun j _ ↦ Nat.zero_le
                (if loop j = d ∨ loop j = ons_dartRev L d then 1 else 0))
              (Finset.mem_univ k)
      omega
    · have hone :
          (if loop k = d ∨ loop k = ons_dartRev L d then 1 else 0) = 1 := by
        rw [if_pos (Or.inr hk)]
      have hle : 1 ≤
          ∑ j, if loop j = d ∨ loop j = ons_dartRev L d then 1 else 0 := by
        calc
          1 = if loop k = d ∨ loop k = ons_dartRev L d then 1 else 0 := hone.symm
          _ ≤ ∑ j, if loop j = d ∨ loop j = ons_dartRev L d then 1 else 0 :=
            Finset.single_le_sum
              (fun j _ ↦ Nat.zero_le
                (if loop j = d ∨ loop j = ons_dartRev L d then 1 else 0))
              (Finset.mem_univ k)
      omega

theorem ons_decLoopExponent_apply_eq_zero_of_not_mem_edgeFinset
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (edge : ons_DecEdge L)
    (hedge : edge ∉ (ons_decGraph L).edgeFinset) :
    ons_decLoopExponent L d edge = 0 := by
  let q := ons_decLoopWalk L d hvalid
  have hcount := DFunLike.congr_fun
    (ons_decLoopWalk_edgeCount L d hvalid) edge
  have hnot : edge ∉ q.edges := by
    intro he
    apply hedge
    rw [SimpleGraph.mem_edgeFinset]
    exact q.edges_subset_edgeSet he
  have hnotms : edge ∉ (q.edges : Multiset (ons_DecEdge L)) := by
    simpa using hnot
  unfold ons_decWalkEdgeCount at hcount
  rw [Multiset.toFinsupp_apply,
    Multiset.count_eq_zero.mpr hnotms] at hcount
  exact hcount.symm

theorem ons_decFormalLogCoeff_eq_zero_of_offGraph
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (m : ons_DecEdge L →₀ ℕ) (edge : ons_DecEdge L)
    (hedge : edge ∉ (ons_decGraph L).edgeFinset)
    (hmedge : m edge ≠ 0) :
    ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) m = 0 := by
  classical
  unfold ons_decFormalLogCoeff
  have houter :
      (∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
        (∑ d : Fin (r + 1) → ons_Dart L,
          if ons_decLoopExponent L d = m then
            ons_decLoopScalar L ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b) d
          else 0) / ((r : ℂ) + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hinner :
        (∑ d : Fin (r + 1) → ons_Dart L,
          if ons_decLoopExponent L d = m then
            ons_decLoopScalar L ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b) d
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      by_cases hscalar : ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) d = 0
      · simp [hscalar]
      · have hvalid := ons_decLoop_valid_of_scalar_ne_zero
          L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d hscalar
        have hzero := ons_decLoopExponent_apply_eq_zero_of_not_mem_edgeFinset
          L d hvalid edge hedge
        rw [if_neg]
        intro hexponent
        apply hmedge
        rw [← hexponent]
        exact hzero
    rw [hinner, zero_div]
  rw [houter]
  ring

theorem ons_decFormalRoot_coeff_eq_zero_of_offGraph
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (m : ons_DecEdge L →₀ ℕ) (edge : ons_DecEdge L)
    (hedge : edge ∉ (ons_decGraph L).edgeFinset)
    (hmedge : m edge ≠ 0) :
    MvPowerSeries.coeff m
      (ons_decFormalRoot L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)) = 0 := by
  classical
  unfold ons_decFormalRoot
  rw [PowerSeries.coeff_subst
    (ons_decFormalLog_hasSubst L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b))]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  apply smul_eq_zero.mpr
  right
  rw [MvPowerSeries.coeff_pow]
  apply Finset.sum_eq_zero
  intro g hg
  have hsum := congrArg (fun x : ons_DecEdge L →₀ ℕ ↦ x edge)
    (Finset.mem_finsuppAntidiag.mp hg).1
  simp only [Finsupp.finsetSum_apply] at hsum
  have hexists : ∃ i ∈ Finset.range n, g i edge ≠ 0 := by
    by_contra hnone
    have hall : ∀ i ∈ Finset.range n, g i edge = 0 := by
      intro i hi
      exact not_ne_iff.mp (fun hne ↦ hnone ⟨i, hi, hne⟩)
    have hzero : ∑ i ∈ Finset.range n, g i edge = 0 :=
      Finset.sum_eq_zero hall
    rw [hzero] at hsum
    exact hmedge hsum.symm
  obtain ⟨i, hi, hgi⟩ := hexists
  apply Finset.prod_eq_zero hi
  change ons_decFormalLogCoeff L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) (g i) = 0
  exact ons_decFormalLogCoeff_eq_zero_of_offGraph
    L a b (g i) edge hedge hgi

end StatMech.Onsager
