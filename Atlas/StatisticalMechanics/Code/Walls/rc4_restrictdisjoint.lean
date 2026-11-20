/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































import Code.Walls.rc4_differagreesets
import Code.Walls.rc3_minimalwitnessencoded

open Finset Set
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]














theorem rc4_restrict_disjoint (k : ConfigSpace α × ConfigSpace α) {K L : Finset α}
    (h : Disjoint K L) :
    Disjoint (K ∩ rc4_differSet k) (L ∩ rc4_differSet k) :=
  h.mono Finset.inter_subset_left Finset.inter_subset_left







theorem rc4_restrict_disjoint_subtype (k : ConfigSpace α × ConfigSpace α) {K L : Finset α}
    (h : Disjoint K L) :
    Disjoint (K.subtype (· ∈ rc4_differSet k)) (L.subtype (· ∈ rc4_differSet k)) := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hxK hxL
  rw [Finset.mem_subtype] at hxK hxL
  exact h hxK hxL




theorem rc4_map_subtype_restrict (k : ConfigSpace α × ConfigSpace α) (K : Finset α) :
    (K.subtype (· ∈ rc4_differSet k)).map (Function.Embedding.subtype _)
      = K ∩ rc4_differSet k := by
  rw [Finset.subtype_map]
  rfl

omit [DecidableEq α] in




theorem rc4_restrict_disjoint_set (k : ConfigSpace α × ConfigSpace α) {K L : Set α}
    (h : Disjoint K L) :
    Disjoint (K ∩ (rc4_differSet k : Set α)) (L ∩ (rc4_differSet k : Set α)) :=
  h.mono Set.inter_subset_left Set.inter_subset_left














theorem rc4_witnesses_restrict_disjoint (k : ConfigSpace α × ConfigSpace α)
    {A B : Set (ConfigSpace α)} {ω : ConfigSpace α} (hω : ω ∈ disjointOccurrence A B) :
    ∃ s K L : Finset α, SupportEncodedMinimalWitness A B ω s K L
        ∧ Disjoint (K ∩ rc4_differSet k) (L ∩ rc4_differSet k)
        ∧ Disjoint (K.subtype (· ∈ rc4_differSet k)) (L.subtype (· ∈ rc4_differSet k)) := by
  obtain ⟨s, K, L, hwit⟩ := exists_supportEncodedMinimalWitness hω
  exact ⟨s, K, L, hwit, rc4_restrict_disjoint k hwit.disjoint,
    rc4_restrict_disjoint_subtype k hwit.disjoint⟩

end StatMech.Walls
