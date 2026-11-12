/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationEmbedding





namespace StatMech.Onsager

theorem ons_decEmbedWalk_support_disjoint
    (L : ℕ) [Fact (2 < L)]
    {u v x y : ons_Dart L}
    (p : (ons_decGraph L).Walk u v)
    (r : (ons_decGraph L).Walk x y)
    (hdisj : List.Disjoint p.support r.support) :
    List.Disjoint (ons_decEmbedWalk L p).support
      (ons_decEmbedWalk L r).support := by
  have hne {a b : ons_Dart L} (ha : a ∈ p.support) (hb : b ∈ r.support) :
      a ≠ b := by
    intro hab
    subst b
    exact (List.disjoint_left.mp hdisj) ha hb
  have hsnd (a : (ons_decGraph L).Dart) (ha : a ∈ p.darts)
      (b : (ons_decGraph L).Dart) (hb : b ∈ r.darts) :
      a.snd ≠ b.snd :=
    hne (p.dart_snd_mem_support_of_mem_darts ha)
      (r.dart_snd_mem_support_of_mem_darts hb)
  have hedge (a : (ons_decGraph L).Dart) (ha : a ∈ p.darts)
      (b : (ons_decGraph L).Dart) (hb : b ∈ r.darts) :
      a.edge ≠ b.edge := by
    intro hab
    change s(a.fst, a.snd) = s(b.fst, b.snd) at hab
    rcases Sym2.eq_iff.mp hab with hab | hab
    · exact hne (p.dart_fst_mem_support_of_mem_darts ha)
        (r.dart_fst_mem_support_of_mem_darts hb) hab.1
    · exact hne (p.dart_fst_mem_support_of_mem_darts ha)
        (r.dart_snd_mem_support_of_mem_darts hb) hab.1
  rw [List.disjoint_left]
  intro z hzp hzr
  rw [SimpleGraph.Walk.mem_support_iff] at hzp hzr
  rcases hzp with hzp | hzp <;> rcases hzr with hzr | hzr
  · apply hne p.start_mem_support r.start_mem_support
    exact ons_decEmbedVertex_injective L (hzp.symm.trans hzr)
  · subst z
    rw [ons_decEmbedWalk_tail_support, List.mem_flatMap] at hzr
    rcases hzr with ⟨b, hb, hub⟩
    rw [ons_mem_decDartSegment_iff] at hub
    rcases hub with hub | hub
    · exact ons_decEmbedVertex_not_mem_route_interior
        L u b.fst b.snd b.adj hub
    · apply hne p.start_mem_support
        (r.dart_snd_mem_support_of_mem_darts hb)
      exact ons_decEmbedVertex_injective L hub
  · subst z
    rw [ons_decEmbedWalk_tail_support, List.mem_flatMap] at hzp
    rcases hzp with ⟨a, ha, hua⟩
    rw [ons_mem_decDartSegment_iff] at hua
    rcases hua with hua | hua
    · exact ons_decEmbedVertex_not_mem_route_interior
        L x a.fst a.snd a.adj hua
    · apply hne (p.dart_snd_mem_support_of_mem_darts ha)
        r.start_mem_support
      exact ons_decEmbedVertex_injective L hua.symm
  · rw [ons_decEmbedWalk_tail_support, List.mem_flatMap] at hzp hzr
    rcases hzp with ⟨a, ha, hza⟩
    rcases hzr with ⟨b, hb, hzb⟩
    exact (List.disjoint_left.mp
      (ons_decDartSegment_disjoint L a b
        (hedge a ha b hb) (hsnd a ha b hb))) hza hzb

theorem ons_decEmbedWalk_support_disjoint_of_toSubgraph
    (L : ℕ) [Fact (2 < L)]
    {u v x y : ons_Dart L}
    (p : (ons_decGraph L).Walk u v)
    (r : (ons_decGraph L).Walk x y)
    (hdisj : Disjoint p.toSubgraph.verts r.toSubgraph.verts) :
    List.Disjoint (ons_decEmbedWalk L p).support
      (ons_decEmbedWalk L r).support := by
  apply ons_decEmbedWalk_support_disjoint L p r
  rw [List.disjoint_left]
  intro z hzp hzr
  exact Set.disjoint_left.mp hdisj
    ((p.mem_verts_toSubgraph).mpr hzp)
    ((r.mem_verts_toSubgraph).mpr hzr)

end StatMech.Onsager
