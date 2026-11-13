/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.KWWeightedCancellation
import Code.Onsager.ShermanPhaseAssembly








namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_weightedPhaseBucketE
    (L : ℕ) [NeZero L]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (a b : Fin 2)
    (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight (ons_KWmatWeightedPhase L weight omega
      (ons_spinPhase L a) (ons_spinPhase L b)) d

noncomputable def ons_weightedPhaseBucketN
    (L : ℕ) [NeZero L]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (a b : Fin 2)
    (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight (ons_KWmatWeightedPhase L weight omega
      (ons_spinPhase L a) (ons_spinPhase L b)) d

noncomputable def ons_maskWeightedPhaseBucketE
    (L : ℕ) [NeZero L]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (a b : Fin 2)
    (forbidden : Finset (ons_Dart L)) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight
      (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega
        (ons_spinPhase L a) (ons_spinPhase L b))) d

noncomputable def ons_maskWeightedPhaseBucketN
    (L : ℕ) [NeZero L]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (a b : Fin 2)
    (forbidden : Finset (ons_Dart L)) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight
      (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega
        (ons_spinPhase L a) (ons_spinPhase L b))) d

theorem ons_KWmatWeightedPhase_loopSum_two_bucket
    {L : ℕ} [NeZero L] [Fact (2 < L)] {n : ℕ}
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (e : ons_Dart L) :
    (∑ d : Fin (n + 1) → ons_Dart L,
      ons_loopWeight (ons_KWmatWeightedPhase L weight omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d) =
      2 * ons_weightedPhaseBucketE L weight omega a b e n +
        ons_weightedPhaseBucketN L weight omega a b e n := by
  let M := ons_KWmatWeightedPhase L weight omega
    (ons_spinPhase L a) (ons_spinPhase L b)
  let P : (Fin (n + 1) → ons_Dart L) → Prop := fun d => ∃ i, d i = e
  let Q : (Fin (n + 1) → ons_Dart L) → Prop := fun d =>
    ∃ j, d j = ons_dartRev L e
  have hsplit := ons_sum_split_by_two P Q (fun d => ons_loopWeight M d)
  have hboth := ons_loopSum_KWmatWeightedPhase_both_zero
    n weight omega homega a b e
  have hsymm := ons_loopSum_KWmatWeightedPhase_symm
    (L := L) (n := n + 1) weight omega homega a b e
  have hset :
      Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
        (∃ i, d i = ons_dartRev L e) ∧ ¬ ∃ j, d j = e) =
      Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
        ¬ (∃ i, d i = e) ∧ ∃ j, d j = ons_dartRev L e) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hset] at hsymm
  simp only [P, Q, M] at hsplit
  unfold ons_weightedPhaseBucketE ons_weightedPhaseBucketN
  linear_combination hsplit + hboth - hsymm

theorem ons_KWmatWeightedPhase_mask_loopSum_two_bucket
    {L : ℕ} [NeZero L] [Fact (2 < L)] {n : ℕ}
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    (∑ d : Fin (n + 1) → ons_Dart L,
      ons_loopWeight
        (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega
          (ons_spinPhase L a) (ons_spinPhase L b))) d) =
      2 * ons_maskWeightedPhaseBucketE L weight omega a b forbidden e n +
        ons_maskWeightedPhaseBucketN L weight omega a b forbidden e n := by
  let M := ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega
    (ons_spinPhase L a) (ons_spinPhase L b))
  let P : (Fin (n + 1) → ons_Dart L) → Prop := fun d => ∃ i, d i = e
  let Q : (Fin (n + 1) → ons_Dart L) → Prop := fun d =>
    ∃ j, d j = ons_dartRev L e
  have hsplit := ons_sum_split_by_two P Q (fun d => ons_loopWeight M d)
  have hboth := ons_loopSum_KWmatWeightedPhase_mask_both_zero
    n weight omega homega a b forbidden hforbidden e
  have hsymm := ons_loopSum_KWmatWeightedPhase_mask_symm
    (L := L) (n := n + 1) weight omega homega a b
    forbidden hforbidden e
  have hset :
      Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
        (∃ i, d i = ons_dartRev L e) ∧ ¬ ∃ j, d j = e) =
      Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
        ¬ (∃ i, d i = e) ∧ ∃ j, d j = ons_dartRev L e) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hset] at hsymm
  simp only [P, Q, M] at hsplit
  unfold ons_maskWeightedPhaseBucketE ons_maskWeightedPhaseBucketN
  linear_combination hsplit + hboth - hsymm

end StatMech.Onsager
