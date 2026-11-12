/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.KWWeightedLemma5

/-!

# Loop cancellations for edge-weighted Kac-Ward matrices

Masked versions of Sherman's Lemma 5 and of reversal symmetry for edge-weighted twisted Kac-Ward
matrices.

## i. Overview

For the edge-weighted twisted Kac-Ward matrix, with a reversal-closed set of darts masked, the
closed walks through a dart and its reverse have total weight zero, and the walks through the dart
and through its reverse contribute equally. These are the two cancellations needed at each step of
Sherman's elimination of darts.

## ii. Key results

- `ons_loopSum_KWmatWeightedPhase_mask_both_zero` : masked Lemma 5
- `ons_loopSum_KWmatWeightedPhase_mask_symm` : masked reversal symmetry

## iii. Table of contents

- A. Masked Lemma 5
- B. Reversal symmetry

## iv. References

- S. Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I. A conjecture of
  Feynman on paths and graphs*, J. Math. Phys. 1 (1960) 202-217

-/

@[expose] public section

namespace StatMech.Onsager

open Matrix BigOperators

/-! ## A. Masked Lemma 5 -/

lemma ons_KWmatWeightedPhase_mask_surgery_sign
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
  · rw [ite_eq_left h, ite_eq_left (hhit.mpr h)]
    simp
  · rw [ite_eq_right h, ite_eq_right (fun hs => h (hhit.mp hs))]
    exact ons_KWmatWeightedPhase_surgery_sign
      weight omega homega a b e d hd

lemma ons_KWmatWeightedPhase_mask_lemma5
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

lemma ons_loopSum_KWmatWeightedPhase_both_zero
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

lemma ons_loopSum_KWmatWeightedPhase_mask_both_zero
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

/-! ## B. Reversal symmetry -/

lemma ons_loopWeight_KWmatWeightedPhase_mask_loopRev
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
  · rw [ite_eq_left h, ite_eq_left (hhit.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun hr => h (hhit.mp hr))]
    exact ons_loopWeight_KWmatWeightedPhase_loopRev
      weight omega homega a b d

lemma ons_loopSum_KWmatWeightedPhase_symm
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

lemma ons_loopSum_KWmatWeightedPhase_mask_symm
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
