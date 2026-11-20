/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWStrictAxisSourcePartition










open Finset SimpleGraph Set MeasureTheory

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section


def rlc_strictLowerHalf : Set (Site 2) := {z | z 1 < 0}



abbrev RlcInsetRightSourcePath (n : Int) :=
  RlcRestrictedCrossingPath 1 (2 * n) (-n) n
    rlc_strictLowerHalf rlc_upperHalf


def rlc_insetRightSourceCoreEvent (n : Int) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_lrRestrictedEvent 1 (2 * n) (-n) n
    rlc_strictLowerHalf rlc_upperHalf


noncomputable def rlc_insetRightHom (n : Int) :
    ((hypercubicLattice 2).induce (rect 1 (2 * n) (-n) n)) →g
      ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)) where
  toFun z := ⟨z, by
    have hz := z.2
    rw [mem_rect] at hz ⊢
    omega⟩
  map_rel' := by
    intro a b hab
    exact hab

theorem rlc_insetRightHom_injective (n : Int) :
    Function.Injective (rlc_insetRightHom n) := by
  intro x y h
  apply Subtype.ext
  exact congrArg
    (fun z : rect 0 (2 * n) (-n) n => (z : Site 2)) h


noncomputable def rlc_insetRightAttachedPath {n : Int}
    (gamma : RlcInsetRightSourcePath n) : RlcRightDiagonalPath n := by
  let x : leftSide 0 (2 * n) (-n) n :=
    ⟨![0, (gamma.1.1 : Site 2) 1], by
      rw [mem_leftSide, mem_rect]
      have h := gamma.1.1.2
      rw [mem_leftSide, mem_rect] at h
      simp
      omega⟩
  let y : rightSide 0 (2 * n) (-n) n := ⟨gamma.1.2.1, by
    rw [mem_rightSide]
    have h := gamma.1.2.1.2
    rw [mem_rightSide] at h
    exact ⟨by
      rw [mem_rect] at h ⊢
      omega, h.2⟩⟩
  let p0 := gamma.1.2.2.1.map (rlc_insetRightHom n)
  let gx : rect 0 (2 * n) (-n) n := ⟨gamma.1.1, by
    have h := gamma.1.1.2
    rw [mem_leftSide, mem_rect] at h
    rw [mem_rect]
    omega⟩
  let gy : rect 0 (2 * n) (-n) n := ⟨gamma.1.2.1, by
    have h := gamma.1.2.1.2
    rw [mem_rightSide, mem_rect] at h
    rw [mem_rect]
    omega⟩
  let p : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Walk gx gy :=
    p0.copy (by apply Subtype.ext; rfl) (by apply Subtype.ext; rfl)
  have hadj : ((hypercubicLattice 2).induce
      (rect 0 (2 * n) (-n) n)).Adj
      ⟨x, leftSide_subset x.2⟩ gx := by
    change (hypercubicLattice 2).Adj
      (![0, (gamma.1.1 : Site 2) 1] : Site 2) (gamma.1.1 : Site 2)
    have hx := gamma.1.1.2.2
    simp [hypercubicLattice_adj, Fin.sum_univ_two, hx]
  let w := SimpleGraph.Walk.cons hadj p
  have hp : p.IsPath := by
    simpa [p, SimpleGraph.Walk.isPath_copy] using
      gamma.1.2.2.1.map_isPath_of_injective
        (rlc_insetRightHom_injective n) gamma.1.2.2.2
  have hxNot : (⟨x, leftSide_subset x.2⟩ :
      rect 0 (2 * n) (-n) n) ∉ p.support := by
    intro hmem
    simp only [p, SimpleGraph.Walk.support_copy, p0,
      SimpleGraph.Walk.support_map, List.mem_map] at hmem
    obtain ⟨z, _hz, heq⟩ := hmem
    have heq0 := congrArg
      (fun u : rect 0 (2 * n) (-n) n => (u : Site 2) 0) heq
    have hz0 : 1 ≤ (z : Site 2) 0 := by
      have hzmem := z.2
      rw [mem_rect] at hzmem
      omega
    change (z : Site 2) 0 = 0 at heq0
    omega
  have hw : w.IsPath := hp.cons hxNot
  refine ⟨⟨x, y, ⟨w, hw⟩⟩, ?_, gamma.2.2⟩
  change (gamma.1.1 : Site 2) 1 ≤ 0
  exact le_of_lt gamma.2.1


noncomputable def rlc_insetRightAttachmentEdge {n : Int}
    (gamma : RlcInsetRightSourcePath n) : Sym2 (Site 2) :=
  s((![0, (gamma.1.1 : Site 2) 1] : Site 2),
    (gamma.1.1 : Site 2))


theorem rlc_insetRightAttachmentEdge_not_mem_pathEdges {n : Int}
    (gamma delta : RlcInsetRightSourcePath n) :
    rlc_insetRightAttachmentEdge gamma ∉ rlc_pathEdges delta.1 := by
  intro he
  have hends := rlc_pathEdge_endpoints_mem_vertices delta.1 he
  have hrect := rlc_pathVertex_mem_rect delta.1 hends.1
  rw [mem_rect] at hrect
  simp at hrect



theorem rlc_insetRightAttachedPath_pathEdges_subset {n : Int}
    (gamma : RlcInsetRightSourcePath n) :
    rlc_pathEdges (rlc_insetRightAttachedPath gamma).1 ⊆
      insert (rlc_insetRightAttachmentEdge gamma)
        (rlc_pathEdges gamma.1) := by
  intro e he
  simp only [rlc_pathEdges, rlc_insetRightAttachedPath,
    SimpleGraph.Walk.edges_cons, rlc_insetRightAttachmentEdge,
    Finset.mem_insert, Finset.mem_image, List.mem_toFinset] at he ⊢
  obtain ⟨a, ha, rfl⟩ := he
  rw [List.mem_cons] at ha
  rcases ha with rfl | ha
  · left
    rfl
  · right
    simp only [SimpleGraph.Walk.edges_copy,
      SimpleGraph.Walk.edges_map, List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    refine ⟨b, hb, ?_⟩
    induction b using Sym2.inductionOn with
    | _ u v => rfl



theorem rlc_insetRightAttachedPath_open {n : Int}
    (gamma : RlcInsetRightSourcePath n)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hgamma : omega ∈ rlc_pathOpen gamma.1)
    (hattach : omega (rlc_insetRightAttachmentEdge gamma) = true) :
    omega ∈ rlc_pathOpen (rlc_insetRightAttachedPath gamma).1 := by
  intro e he
  rcases Finset.mem_insert.mp
      (rlc_insetRightAttachedPath_pathEdges_subset gamma he) with he | he
  · simpa [he] using hattach
  · exact hgamma e he



theorem rlc_insetRightAttachedPath_axis_strict {n : Int}
    (gamma : RlcInsetRightSourcePath n) :
    ∀ {z : Site 2},
      z ∈ rlc_pathVertices (rlc_insetRightAttachedPath gamma).1 ->
      z 0 = 0 -> z 1 < 0 := by
  intro z hz hz0
  simp only [rlc_pathVertices, rlc_insetRightAttachedPath,
    Finset.mem_image, List.mem_toFinset,
    SimpleGraph.Walk.support_cons, List.mem_cons] at hz
  obtain ⟨u, hu | hu, huz⟩ := hz
  · subst hu
    simpa [rlc_strictLowerHalf, ← huz] using gamma.2.1
  · simp only [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_map, List.mem_map] at hu
    obtain ⟨v, _hv, hvu⟩ := hu
    have hv0 : 1 ≤ (v : Site 2) 0 := by
      have hmem := v.2
      rw [mem_rect] at hmem
      omega
    have hzu := congrArg
      (fun q : rect 0 (2 * n) (-n) n => (q : Site 2) 0) hvu
    have hu0 : (u : Site 2) 0 = 0 := by
      rw [huz]
      exact hz0
    change (v : Site 2) 0 = (u : Site 2) 0 at hzu
    omega



theorem rlc_insetRightSourceCore_to_strictAxis_mass
    (p : NNReal) (hp : p ≤ 1) (n : Int) :
    (p : Real) *
        (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
          (rlc_insetRightSourceCoreEvent n) ≤
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
        (rlc_strictAxisRightSourceEvent n) := by
  let I := RlcInsetRightSourcePath n
  let N := Fintype.card I
  let path : Fin N → I := (Fintype.equivFin I).symm
  let W : Fin N → Set (ConfigSpace (Sym2 (Site 2))) :=
    fun i => rlc_pathOpen (path i).1
  let X : Fin N → Set (ConfigSpace (Sym2 (Site 2))) :=
    fun i => {omega | omega (rlc_insetRightAttachmentEdge (path i)) = true}
  let T : Fin N → Finset (Sym2 (Site 2)) :=
    fun i => rlc_pathEdges (path i).1
  let U : Fin N → Finset (Sym2 (Site 2)) :=
    fun i => {rlc_insetRightAttachmentEdge (path i)}
  have hcover : (⋃ i, W i) = rlc_insetRightSourceCoreEvent n := by
    rw [rlc_insetRightSourceCoreEvent,
      ← rlc_iUnion_restrictedPathOpen]
    ext omega
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨path i, ?_⟩
      simpa [W] using hi
    · rintro ⟨gamma, hgamma⟩
      refine ⟨Fintype.equivFin I gamma, ?_⟩
      simpa [W, path] using hgamma
  rw [← hcover]
  apply rlc_exploration_lower_bound p hp W X T U
    (rlc_strictAxisRightSourceEvent n) (p : Real)
  · exact_mod_cast p.2
  · intro i
    exact rlc_pathOpen_dependsOn (path i).1
  · intro i
    simpa [X, U] using
      coord_true_dependsOn (rlc_insetRightAttachmentEdge (path i))
  · intro i
    rw [Finset.disjoint_left]
    intro e heT heU
    have heEq : e = rlc_insetRightAttachmentEdge (path i) := by
      simpa [U] using heU
    subst e
    simp only [rlc_exploredSupport, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_univ, true_and] at heT
    obtain ⟨j, _hji, hePath⟩ := heT
    exact rlc_insetRightAttachmentEdge_not_mem_pathEdges
      (path i) (path j) hePath
  · intro i
    simpa [X] using
      (coord_true_prob (E := Sym2 (Site 2)) p hp
        (rlc_insetRightAttachmentEdge (path i))).ge
  · intro i omega homega
    have hpath : omega ∈ rlc_pathOpen (path i).1 :=
      (rlc_mem_firstWitness_iff.mp homega.1).1
    have hopen := rlc_insetRightAttachedPath_open
      (path i) hpath homega.2
    apply Set.mem_iUnion.mpr
    exact ⟨⟨rlc_insetRightAttachedPath (path i),
      rlc_insetRightAttachedPath_axis_strict (path i)⟩, hopen⟩

end

end StatMech.Universality
