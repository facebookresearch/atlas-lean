/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.KWWeightedLemma5









namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_KWmatWeightedPhase_mask_surgery_sign
    {L n : ℕ} [NeZero L] [NeZero n] [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) (d : Fin n → ons_Dart L)
    (hd : d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
    ons_loopWeight
        (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega
          (ons_spinPhase L a) (ons_spinPhase L b)))
        (ons_surgery e (ons_dartRev L) d) =
      -ons_loopWeight
        (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega
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
    exact ons_KWmatWeightedPhase_surgery_sign
      weight omega homega a b e d hd

theorem ons_KWmatWeightedPhase_mask_lemma5
    {L n : ℕ} [NeZero L] [NeZero n] [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    ∑ d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e),
      ons_loopWeight
        (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega
          (ons_spinPhase L a) (ons_spinPhase L b))) d = 0 := by
  apply ons_lemma5 _ e (ons_dartRev L)
    (ons_dartRev_involutive L) (ons_dartRev_ne L e)
  intro d hd
  exact ons_KWmatWeightedPhase_mask_surgery_sign weight omega homega
    a b forbidden hforbidden e d hd

theorem ons_loopSum_KWmatWeightedPhase_both_zero
    {L : ℕ} [NeZero L] [Fact (2 < L)]
    (n : ℕ) (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (e : ons_Dart L) :
    (∑ d ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter
        (fun d => (∃ i, d i = e) ∧ (∃ j, d j = ons_dartRev L e)),
      ons_loopWeight (ons_KWmatWeightedPhase L weight omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d) = 0 := by
  have hset :
      ((Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter
        (fun d => (∃ i, d i = e) ∧ (∃ j, d j = ons_dartRev L e))) =
        ons_loopSetBoth (n := n + 1) e (ons_dartRev L e) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ons_mem_loopSetBoth]
  rw [hset]
  exact ons_KWmatWeightedPhase_lemma5 weight omega homega a b e

theorem ons_loopSum_KWmatWeightedPhase_mask_both_zero
    {L : ℕ} [NeZero L] [Fact (2 < L)]
    (n : ℕ) (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    (∑ d ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter
        (fun d => (∃ i, d i = e) ∧ (∃ j, d j = ons_dartRev L e)),
      ons_loopWeight
        (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega
          (ons_spinPhase L a) (ons_spinPhase L b))) d) = 0 := by
  have hset :
      ((Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter
        (fun d => (∃ i, d i = e) ∧ (∃ j, d j = ons_dartRev L e))) =
        ons_loopSetBoth (n := n + 1) e (ons_dartRev L e) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ons_mem_loopSetBoth]
  rw [hset]
  exact ons_KWmatWeightedPhase_mask_lemma5 weight omega homega
    a b forbidden hforbidden e

theorem ons_loopWeight_KWmatWeightedPhase_mask_loopRev
    {L n : ℕ} [NeZero L] [NeZero n]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (d : Fin n → ons_Dart L) :
    ons_loopWeight
        (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega
          (ons_spinPhase L a) (ons_spinPhase L b))) (ons_loopRev L d) =
      ons_loopWeight
        (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega
          (ons_spinPhase L a) (ons_spinPhase L b))) d := by
  have hhit := ons_loopRev_hits_iff forbidden hforbidden d
  rw [ons_loopWeight_maskMatrix, ons_loopWeight_maskMatrix]
  by_cases h : ∃ k, d k ∈ forbidden
  · rw [if_pos h, if_pos (hhit.mpr h)]
  · rw [if_neg h, if_neg (fun hr => h (hhit.mp hr))]
    exact ons_loopWeight_KWmatWeightedPhase_loopRev
      weight omega homega a b d

theorem ons_loopSum_KWmatWeightedPhase_symm
    {L n : ℕ} [NeZero L] [NeZero n]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (e : ons_Dart L) :
    (∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L =>
        (∃ i, d i = e) ∧ ¬ ∃ j, d j = ons_dartRev L e)),
        ons_loopWeight (ons_KWmatWeightedPhase L weight omega
          (ons_spinPhase L a) (ons_spinPhase L b)) d) =
      ∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L =>
        (∃ i, d i = ons_dartRev L e) ∧ ¬ ∃ j, d j = e)),
        ons_loopWeight (ons_KWmatWeightedPhase L weight omega
          (ons_spinPhase L a) (ons_spinPhase L b)) d := by
  refine Finset.sum_nbij' (ons_loopRev L) (ons_loopRev L) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hd
    constructor
    · rw [ons_visits_loopRev, ons_dartRev_involutive L e]
      exact ⟨i, hie⟩
    · rwa [ons_visits_loopRev]
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hd
    constructor
    · rw [ons_visits_loopRev]
      exact ⟨i, hie⟩
    · rwa [ons_visits_loopRev, ons_dartRev_involutive L e]
  · exact fun d _ => ons_loopRev_involutive L n d
  · exact fun d _ => ons_loopRev_involutive L n d
  · intro d _
    exact (ons_loopWeight_KWmatWeightedPhase_loopRev
      weight omega homega a b d).symm

theorem ons_loopSum_KWmatWeightedPhase_mask_symm
    {L n : ℕ} [NeZero L] [NeZero n]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    (∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L =>
        (∃ i, d i = e) ∧ ¬ ∃ j, d j = ons_dartRev L e)),
        ons_loopWeight
          (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega
            (ons_spinPhase L a) (ons_spinPhase L b))) d) =
      ∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L =>
        (∃ i, d i = ons_dartRev L e) ∧ ¬ ∃ j, d j = e)),
        ons_loopWeight
          (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega
            (ons_spinPhase L a) (ons_spinPhase L b))) d := by
  refine Finset.sum_nbij' (ons_loopRev L) (ons_loopRev L) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hd
    constructor
    · rw [ons_visits_loopRev, ons_dartRev_involutive L e]
      exact ⟨i, hie⟩
    · rwa [ons_visits_loopRev]
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hd
    constructor
    · rw [ons_visits_loopRev]
      exact ⟨i, hie⟩
    · rwa [ons_visits_loopRev, ons_dartRev_involutive L e]
  · exact fun d _ => ons_loopRev_involutive L n d
  · exact fun d _ => ons_loopRev_involutive L n d
  · intro d _
    exact (ons_loopWeight_KWmatWeightedPhase_mask_loopRev weight omega homega
      a b forbidden hforbidden d).symm

end StatMech.Onsager
