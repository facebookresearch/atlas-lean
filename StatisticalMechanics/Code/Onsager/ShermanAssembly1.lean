/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.KWLemma5
import Code.Onsager.ShermanLemma5
import Code.Onsager.ShermanLoop
import Code.Onsager.KWMatrix
import Code.Onsager.DetWalkExp












































namespace StatMech.Onsager

open Matrix BigOperators Finset












theorem ons_sum_split_by_two {β : Type*} [Fintype β] (P Q : β → Prop)
    [DecidablePred P] [DecidablePred Q] (f : β → ℂ) :
    (∑ v ∈ (Finset.univ : Finset β), f v)
      = (∑ v ∈ Finset.univ.filter (fun v => ¬ P v ∧ ¬ Q v), f v)
        + (∑ v ∈ Finset.univ.filter (fun v => P v ∧ ¬ Q v), f v)
        + (∑ v ∈ Finset.univ.filter (fun v => ¬ P v ∧ Q v), f v)
        + (∑ v ∈ Finset.univ.filter (fun v => P v ∧ Q v), f v) := by
  have hP := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset β) P f
  have hPQ := Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset β).filter P) Q f
  have hnPQ := Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset β).filter (fun v => ¬ P v)) Q f
  simp only [Finset.filter_filter] at hPQ hnPQ
  linear_combination -hP - hPQ - hnPQ



section KW

variable {L : ℕ} [NeZero L]







theorem ons_KW_loopSum_split_four (n : ℕ) (x ω : ℂ) (e : ons_Dart L) :
    (∑ v ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)),
        ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1)))
      = (∑ v ∈ Finset.univ.filter
            (fun v : Fin (n + 1) → ons_Dart L =>
              ¬ (∃ i, v i = e) ∧ ¬ (∃ j, v j = ons_dartRev L e)),
          ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1)))
        + (∑ v ∈ Finset.univ.filter
            (fun v : Fin (n + 1) → ons_Dart L =>
              (∃ i, v i = e) ∧ ¬ (∃ j, v j = ons_dartRev L e)),
          ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1)))
        + (∑ v ∈ Finset.univ.filter
            (fun v : Fin (n + 1) → ons_Dart L =>
              ¬ (∃ i, v i = e) ∧ (∃ j, v j = ons_dartRev L e)),
          ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1)))
        + (∑ v ∈ Finset.univ.filter
            (fun v : Fin (n + 1) → ons_Dart L =>
              (∃ i, v i = e) ∧ (∃ j, v j = ons_dartRev L e)),
          ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1))) :=
  ons_sum_split_by_two (fun v : Fin (n + 1) → ons_Dart L => ∃ i, v i = e)
    (fun v : Fin (n + 1) → ons_Dart L => ∃ j, v j = ons_dartRev L e)
    (fun v : Fin (n + 1) → ons_Dart L =>
      ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1)))







theorem ons_loopSum_both_zero [Fact (2 < L)] (n : ℕ) (x ω : ℂ) (hω : ω ^ 2 = Complex.I)
    (e : ons_Dart L) :
    (∑ v ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter
        (fun v => (∃ i, v i = e) ∧ (∃ j, v j = ons_dartRev L e)),
      ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1))) = 0 := by
  have hset : ((Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter
        (fun v => (∃ i, v i = e) ∧ (∃ j, v j = ons_dartRev L e)))
      = ons_loopSetBoth (n := n + 1) e (ons_dartRev L e) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ons_mem_loopSetBoth]
  rw [hset]
  simpa only [ons_loopWeight] using ons_KW_lemma5 (n := n + 1) x ω hω e










theorem ons_KW_loopSum_no_both [Fact (2 < L)] (n : ℕ) (x ω : ℂ) (hω : ω ^ 2 = Complex.I)
    (e : ons_Dart L) :
    (∑ v ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)),
        ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1)))
      = (∑ v ∈ Finset.univ.filter
            (fun v : Fin (n + 1) → ons_Dart L =>
              (∃ i, v i = e) ∧ ¬ (∃ j, v j = ons_dartRev L e)),
          ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1)))
        + (∑ v ∈ Finset.univ.filter
            (fun v : Fin (n + 1) → ons_Dart L =>
              ¬ (∃ i, v i = e) ∧ (∃ j, v j = ons_dartRev L e)),
          ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1)))
        + (∑ v ∈ Finset.univ.filter
            (fun v : Fin (n + 1) → ons_Dart L =>
              ¬ (∃ i, v i = e) ∧ ¬ (∃ j, v j = ons_dartRev L e)),
          ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1))) := by
  have hsplit := ons_KW_loopSum_split_four (L := L) n x ω e
  have hboth := ons_loopSum_both_zero (L := L) n x ω hω e
  linear_combination hsplit + hboth

end KW

end StatMech.Onsager
