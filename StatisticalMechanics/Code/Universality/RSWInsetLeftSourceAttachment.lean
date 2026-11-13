/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWInsetSourceAttachment









open Finset SimpleGraph Set MeasureTheory
namespace StatMech.Universality
open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box
noncomputable section

def rlc_strictUpperHalf : Set (Site 2) := {z | 0 < z 1}
abbrev RlcInsetLeftSourcePath (n : Int) :=
  RlcRestrictedCrossingPath (-2 * n) (-1) (-n) n rlc_lowerHalf rlc_strictUpperHalf

noncomputable def rlc_insetLeftHom (n : Int) :
    ((hypercubicLattice 2).induce (rect (-2 * n) (-1) (-n) n)) →g
      ((hypercubicLattice 2).induce (rect (-2 * n) 0 (-n) n)) where
  toFun z := ⟨z, by
    have hz:=z.2
    rw [mem_rect] at hz ⊢
    omega⟩
  map_rel' := by intro a b h; exact h

theorem rlc_insetLeftHom_injective (n : Int) : Function.Injective (rlc_insetLeftHom n) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : rect (-2 * n) 0 (-n) n => (z:Site 2)) h

noncomputable def rlc_insetLeftAttachedPath {n : Int} (gamma : RlcInsetLeftSourcePath n) :
    RlcLeftDiagonalPath n := by
  let x : leftSide (-2 * n) 0 (-n) n := ⟨gamma.1.1, by
    rw [mem_leftSide]
    have h:=gamma.1.1.2
    rw [mem_leftSide] at h
    exact ⟨by rw [mem_rect] at h ⊢; omega, h.2⟩⟩
  let y : rightSide (-2 * n) 0 (-n) n :=
    ⟨![0,(gamma.1.2.1:Site 2) 1], by
      rw [mem_rightSide, mem_rect]
      have h:=gamma.1.2.1.2
      rw [mem_rightSide, mem_rect] at h
      simp
      omega⟩
  let p0 := gamma.1.2.2.1.map (rlc_insetLeftHom n)
  let gx : rect (-2 * n) 0 (-n) n := ⟨gamma.1.1, by
    have h:=gamma.1.1.2
    rw [mem_leftSide, mem_rect] at h
    rw [mem_rect]
    omega⟩
  let gy : rect (-2 * n) 0 (-n) n := ⟨gamma.1.2.1, by
    have h:=gamma.1.2.1.2
    rw [mem_rightSide, mem_rect] at h
    rw [mem_rect]
    omega⟩
  let p : ((hypercubicLattice 2).induce (rect (-2 * n) 0 (-n) n)).Walk gx gy :=
    p0.copy (by apply Subtype.ext; rfl) (by apply Subtype.ext; rfl)
  have hadj : ((hypercubicLattice 2).induce (rect (-2 * n) 0 (-n) n)).Adj
      gy ⟨y, rightSide_subset y.2⟩ := by
    change (hypercubicLattice 2).Adj (gamma.1.2.1:Site 2)
      (![0,(gamma.1.2.1:Site 2) 1]:Site 2)
    have hx:=gamma.1.2.1.2.2
    simp [hypercubicLattice_adj, Fin.sum_univ_two, hx]
  let w := p.concat hadj
  have hp : p.IsPath := by
    simpa [p, SimpleGraph.Walk.isPath_copy] using
      gamma.1.2.2.1.map_isPath_of_injective (rlc_insetLeftHom_injective n) gamma.1.2.2.2
  have hyNot : (⟨y,rightSide_subset y.2⟩ : rect (-2 * n) 0 (-n) n)
      ∉ p.support := by
    intro hmem
    simp only [p, SimpleGraph.Walk.support_copy,p0,
      SimpleGraph.Walk.support_map,List.mem_map] at hmem
    obtain ⟨z,_hz,heq⟩:=hmem
    have heq0:=congrArg (fun u : rect (-2 * n) 0 (-n) n => (u:Site 2) 0) heq
    have hz0 : (z:Site 2) 0 ≤ -1 := by
      have hzmem:=z.2
      rw [mem_rect] at hzmem
      omega
    change (z:Site 2) 0 = 0 at heq0
    omega
  have hw : w.IsPath := hp.concat hyNot hadj
  refine ⟨⟨x,y,⟨w,hw⟩⟩,gamma.2.1,?_⟩
  change 0 ≤ (gamma.1.2.1:Site 2) 1
  exact le_of_lt gamma.2.2

noncomputable def rlc_insetLeftAttachmentEdge {n : Int} (gamma : RlcInsetLeftSourcePath n) : Sym2 (Site 2) :=
  s((gamma.1.2.1:Site 2), (![0,(gamma.1.2.1:Site 2) 1]:Site 2))

theorem rlc_insetLeftAttachmentEdge_not_mem_pathEdges {n : Int} (gamma delta : RlcInsetLeftSourcePath n) :
    rlc_insetLeftAttachmentEdge gamma ∉ rlc_pathEdges delta.1 := by
  intro he
  have hends:=rlc_pathEdge_endpoints_mem_vertices delta.1 he
  have hrect:=rlc_pathVertex_mem_rect delta.1 hends.2
  rw [mem_rect] at hrect
  simp at hrect

theorem rlc_insetLeftAttachedPath_pathEdges_subset {n : Int} (gamma : RlcInsetLeftSourcePath n) :
    rlc_pathEdges (rlc_insetLeftAttachedPath gamma).1 ⊆
      insert (rlc_insetLeftAttachmentEdge gamma) (rlc_pathEdges gamma.1) := by
  intro e he
  simp only [rlc_pathEdges,rlc_insetLeftAttachedPath,SimpleGraph.Walk.edges_concat,
    rlc_insetLeftAttachmentEdge,Finset.mem_insert,Finset.mem_image,List.mem_toFinset] at he ⊢
  obtain ⟨a,ha,rfl⟩:=he
  simp only [List.concat_eq_append,List.mem_append,List.mem_singleton] at ha
  rcases ha with ha | rfl
  · right
    simp only [SimpleGraph.Walk.edges_copy,
      SimpleGraph.Walk.edges_map,List.mem_map] at ha
    obtain ⟨b,hb,rfl⟩:=ha
    refine ⟨b,hb,?_⟩
    induction b using Sym2.inductionOn with
    | _ u v => rfl
  · left
    rfl

theorem rlc_insetLeftAttachedPath_open {n : Int} (gamma : RlcInsetLeftSourcePath n)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hg : omega ∈ rlc_pathOpen gamma.1) (he : omega (rlc_insetLeftAttachmentEdge gamma) = true) :
    omega ∈ rlc_pathOpen (rlc_insetLeftAttachedPath gamma).1 := by
  intro e h
  rcases Finset.mem_insert.mp (rlc_insetLeftAttachedPath_pathEdges_subset gamma h) with h | h
  · simpa [h] using he
  · exact hg e h

theorem rlc_insetLeftAttachedPath_axis_strict {n : Int} (gamma : RlcInsetLeftSourcePath n) :
    ∀ {z:Site 2}, z ∈ rlc_pathVertices (rlc_insetLeftAttachedPath gamma).1 ->
      z 0=0 -> 0<z 1 := by
  intro z hz hz0
  simp only [rlc_pathVertices,rlc_insetLeftAttachedPath,Finset.mem_image,List.mem_toFinset,
    SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton] at hz
  obtain ⟨u,hu,huz⟩:=hz
  rcases hu with hu | hu
  · simp only [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_map,List.mem_map] at hu
    obtain ⟨v,_hv,hvu⟩:=hu
    have hv0 : (v:Site 2) 0 ≤ -1 := by
      have hmem:=v.2
      rw [mem_rect] at hmem
      omega
    have hzu:=congrArg (fun q : rect (-2 * n) 0 (-n) n => (q:Site 2) 0) hvu
    have hu0 : (u:Site 2) 0=0 := by rw [huz]; exact hz0
    change (v:Site 2) 0=(u:Site 2) 0 at hzu
    omega
  · subst hu
    simpa [rlc_strictUpperHalf,← huz] using gamma.2.2

def rlc_insetLeftSourceCoreEvent (n : Int) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_lrRestrictedEvent (-2 * n) (-1) (-n) n rlc_lowerHalf rlc_strictUpperHalf

theorem rlc_insetLeftSourceCore_to_strictAxis_mass (p : NNReal) (hp:p≤1) (n : Int) :
    (p : Real)*(bernoulliProductMeasure (E :=Sym2 (Site 2)) p hp).real (rlc_insetLeftSourceCoreEvent n) ≤
      (bernoulliProductMeasure (E :=Sym2 (Site 2)) p hp).real
        (rlc_strictAxisLeftSourceEvent n) := by
  let I:=RlcInsetLeftSourcePath n
  let N:=Fintype.card I
  let path : Fin N → I := (Fintype.equivFin I).symm
  let W : Fin N → Set (ConfigSpace (Sym2 (Site 2))) := fun i=>rlc_pathOpen (path i).1
  let X : Fin N → Set (ConfigSpace (Sym2 (Site 2))) := fun i=>{w|w (rlc_insetLeftAttachmentEdge (path i)) = true}
  let T : Fin N → Finset (Sym2 (Site 2)) := fun i=>rlc_pathEdges (path i).1
  let U : Fin N → Finset (Sym2 (Site 2)) := fun i=>{rlc_insetLeftAttachmentEdge (path i)}
  have hcover:(⋃i,W i)=rlc_insetLeftSourceCoreEvent n := by
    rw [rlc_insetLeftSourceCoreEvent,←rlc_iUnion_restrictedPathOpen]
    ext w
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      refine ⟨path i,?_⟩
      simpa [W] using hi
    · rintro ⟨g,hg⟩
      refine ⟨Fintype.equivFin I g,?_⟩
      simpa [W,path] using hg
  rw [←hcover]
  apply rlc_exploration_lower_bound p hp W X T U
    (rlc_strictAxisLeftSourceEvent n) (p : Real)
  · exact_mod_cast p.2
  · intro i; exact rlc_pathOpen_dependsOn (path i).1
  · intro i; simpa [X,U] using coord_true_dependsOn (rlc_insetLeftAttachmentEdge (path i))
  · intro i
    rw [Finset.disjoint_left]
    intro e ht hu
    have he:e=rlc_insetLeftAttachmentEdge (path i):=by simpa [U] using hu
    subst e
    simp only [rlc_exploredSupport,Finset.mem_biUnion,
      Finset.mem_filter,Finset.mem_univ,true_and] at ht
    obtain ⟨j,_hji,hj⟩:=ht
    exact rlc_insetLeftAttachmentEdge_not_mem_pathEdges (path i) (path j) hj
  · intro i
    simpa [X] using (coord_true_prob (E :=Sym2 (Site 2)) p hp (rlc_insetLeftAttachmentEdge (path i))).ge
  · intro i w hw
    have hg:w∈rlc_pathOpen (path i).1 := (rlc_mem_firstWitness_iff.mp hw.1).1
    have ho:=rlc_insetLeftAttachedPath_open (path i) hg hw.2
    apply Set.mem_iUnion.mpr
    exact ⟨⟨rlc_insetLeftAttachedPath (path i),rlc_insetLeftAttachedPath_axis_strict (path i)⟩,ho⟩

end
end StatMech.Universality
