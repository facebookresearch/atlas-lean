/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceBeadIntervals

/-!
# Actual whole beads in an original concatenation

Every positive original bead of the SAME native concatenation belongs
to exactly one original side of its common pivot. Joint readbacks retain
the two original complete joint sets, including zero-dimensional sides.
-/

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open OriginalTwoBead.OrdinalCharts

/-- Each original first joint has precisely the SAME full concatenated joint membership. -/
theorem concat_prefix_joint_iff (T U : Data) (i : Fin (T.dimension + 1)) :
    prefixEmbedding T.dimension U.dimension i ∈ (T.concat U).joints ↔ i ∈ T.joints := by
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨j, hj, he⟩ := Finset.mem_map.mp hi
      have hji : j = i := (prefixEmbedding T.dimension U.dimension).injective he
      exact hji ▸ hj
    · obtain ⟨j, _hj, he⟩ := Finset.mem_map.mp hi
      have hj0 : j.val = 0 := by
        have hv := congrArg Fin.val he
        change T.dimension + j.val = i.val at hv
        have := i.isLt
        omega
      have hiLast : i = Fin.last T.dimension := by
        apply Fin.ext
        have hv := congrArg Fin.val he
        change T.dimension + j.val = i.val at hv
        change i.val = T.dimension
        omega
      exact hiLast.symm ▸ T.target_joint
  · intro hi
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_map.mpr ⟨i, hi, rfl⟩))

/-- Each original second joint has precisely the SAME full concatenated joint membership. -/
theorem concat_suffix_joint_iff (T U : Data) (i : Fin (U.dimension + 1)) :
    suffix T.dimension U.dimension i ∈ (T.concat U).joints ↔ i ∈ U.joints := by
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨j, _hj, he⟩ := Finset.mem_map.mp hi
      have hi0 : i = 0 := by
        apply Fin.ext
        have hv := congrArg Fin.val he
        change j.val = T.dimension + i.val at hv
        have := j.isLt
        change i.val = 0
        omega
      exact hi0.symm ▸ U.source_joint
    · obtain ⟨j, hj, he⟩ := Finset.mem_map.mp hi
      have hji : j = i := (suffix T.dimension U.dimension).injective he
      exact hji ▸ hj
  · intro hi
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_map.mpr ⟨i, hi, rfl⟩))

/-- Every actual full concatenated bead lies entirely before or after the SAME original pivot. -/
theorem concat_bead_cases (T U : Data) {a b : Fin ((T.concat U).dimension + 1)}
    (h : IsBead (T.concat U) a b) :
    (∃ (c d : Fin (T.dimension + 1)) (_h : IsBead T c d),
      prefixEmbedding T.dimension U.dimension c = a ∧ prefixEmbedding T.dimension U.dimension d = b) ∨
    (∃ (c d : Fin (U.dimension + 1)) (_h : IsBead U c d),
      suffix T.dimension U.dimension c = a ∧ suffix T.dimension U.dimension d = b) := by
  rcases h.consecutive (pivot T.dimension U.dimension) (concat_pivot_joint T U) with ha | hb
  · let c : Fin (U.dimension + 1) := ⟨a.val - T.dimension, by
      change T.dimension ≤ a.val at ha
      have hbound : a.val < T.dimension + U.dimension + 1 := a.isLt
      omega⟩
    let d : Fin (U.dimension + 1) := ⟨b.val - T.dimension, by
      change T.dimension ≤ a.val at ha
      have hp := h.positive
      change a.val < b.val at hp
      have hbound : b.val < T.dimension + U.dimension + 1 := b.isLt
      omega⟩
    have hc : suffix T.dimension U.dimension c = a := by
      apply Fin.ext
      change T.dimension + (a.val - T.dimension) = a.val
      change T.dimension ≤ a.val at ha
      omega
    have hd : suffix T.dimension U.dimension d = b := by
      apply Fin.ext
      change T.dimension + (b.val - T.dimension) = b.val
      change T.dimension ≤ a.val at ha
      have hp := h.positive
      change a.val < b.val at hp
      omega
    refine Or.inr ⟨c, d, ⟨?_, ?_, ?_, ?_⟩, hc, hd⟩
    · exact (concat_suffix_joint_iff T U c).mp (hc.symm ▸ h.source)
    · exact (concat_suffix_joint_iff T U d).mp (hd.symm ▸ h.target)
    · apply (suffix T.dimension U.dimension).lt_iff_lt.mp
      exact hc.symm ▸ hd.symm ▸ h.positive
    · intro k hk
      have hj := (concat_suffix_joint_iff T U k).mpr hk
      rcases h.consecutive (suffix T.dimension U.dimension k) hj with hj | hj
      · exact Or.inl ((suffix T.dimension U.dimension).le_iff_le.mp (hc.symm ▸ hj))
      · exact Or.inr ((suffix T.dimension U.dimension).le_iff_le.mp (hd.symm ▸ hj))
  · let c : Fin (T.dimension + 1) := ⟨a.val, by
      change b.val ≤ T.dimension at hb
      have hp := h.positive
      change a.val < b.val at hp
      omega⟩
    let d : Fin (T.dimension + 1) := ⟨b.val, by change b.val ≤ T.dimension at hb; omega⟩
    have hc : prefixEmbedding T.dimension U.dimension c = a := Fin.ext rfl
    have hd : prefixEmbedding T.dimension U.dimension d = b := Fin.ext rfl
    refine Or.inl ⟨c, d, ⟨?_, ?_, ?_, ?_⟩, hc, hd⟩
    · exact (concat_prefix_joint_iff T U c).mp (hc.symm ▸ h.source)
    · exact (concat_prefix_joint_iff T U d).mp (hd.symm ▸ h.target)
    · apply (prefixEmbedding T.dimension U.dimension).lt_iff_lt.mp
      exact hc.symm ▸ hd.symm ▸ h.positive
    · intro k hk
      have hj := (concat_prefix_joint_iff T U k).mpr hk
      rcases h.consecutive (prefixEmbedding T.dimension U.dimension k) hj with hj | hj
      · exact Or.inl ((prefixEmbedding T.dimension U.dimension).le_iff_le.mp (hc.symm ▸ hj))
      · exact Or.inr ((prefixEmbedding T.dimension U.dimension).le_iff_le.mp (hd.symm ▸ hj))

end SSet.OriginalNecklace
