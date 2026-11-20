/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKMedialToggleMerge
import Code.FrontierD.FKRectZeroTurnMixedCandidates











open Finset

namespace StatMech.FrontierD

noncomputable section


def fkRectDualCutEdges (R : FKRectTorus) : Finset R.EdgeIndex :=
  (fkRectTorusCutEdges R).image (fkRectEdgeToDualEdge R)

@[simp] theorem mem_fkRectDualCutEdges_iff
    (R : FKRectTorus) (e : R.EdgeIndex) :
    e ∈ fkRectDualCutEdges R ↔
      fkRectDualEdgeToEdge R e ∈ fkRectTorusCutEdges R := by
  classical
  constructor
  · intro he
    rw [fkRectDualCutEdges, Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    simpa using ha
  · intro he
    rw [fkRectDualCutEdges, Finset.mem_image]
    exact ⟨fkRectDualEdgeToEdge R e, he, by simp⟩


def fkRectWiredDualAddedEdges
    (R : FKRectTorus) (omega : R.Configuration) : Finset R.EdgeIndex :=
  fkRectDualCutEdges R \
    fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega)

theorem fkRectWiredDualAddedEdges_disjoint_openEdges
    (R : FKRectTorus) (omega : R.Configuration) :
    Disjoint (fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega))
      (fkRectWiredDualAddedEdges R omega) := by
  classical
  rw [Finset.disjoint_left]
  intro e heOpen heAdded
  exact (Finset.mem_sdiff.mp heAdded).2 heOpen



theorem fkRectDualConfiguration_forceCutClosed_apply
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex) :
    fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega) e =
      if e ∈ fkRectDualCutEdges R then true
      else fkRectDualConfigurationEquiv R omega e := by
  rw [fkRectDualConfigurationEquiv_apply,
    fkRectDualConfigurationEquiv_apply]
  by_cases he : e ∈ fkRectDualCutEdges R
  · rw [if_pos he]
    have hcut := (mem_fkRectDualCutEdges_iff R e).1 he
    rw [fkRectForceCutClosed_of_mem R omega _ hcut]
    rfl
  · rw [if_neg he]
    have hcut : fkRectDualEdgeToEdge R e ∉ fkRectTorusCutEdges R := by
      simpa using he
    rw [fkRectForceCutClosed_of_not_mem R omega _ hcut]



theorem fkRectOpenEdges_dual_forceCutClosed
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenEdges R
        (fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega)) =
      fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega) ∪
        fkRectDualCutEdges R := by
  classical
  ext e
  simp only [fkRectOpenEdges, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_union]
  rw [fkRectDualConfiguration_forceCutClosed_apply]
  by_cases he : e ∈ fkRectDualCutEdges R
  · simp [he]
  · simp [he]



theorem fkRectOpenEdges_dual_forceCutClosed_eq_inserted
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenEdges R
        (fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega)) =
      fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega) ∪
        fkRectWiredDualAddedEdges R omega := by
  rw [fkRectOpenEdges_dual_forceCutClosed]
  classical
  ext e
  simp [fkRectWiredDualAddedEdges]



theorem fkRectDual_forceCutClosed_eq_configurationOfInsertedEdges
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega) =
      fkRectConfigurationOfEdges R
        (fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega) ∪
          fkRectWiredDualAddedEdges R omega) := by
  rw [← fkRectOpenEdges_dual_forceCutClosed_eq_inserted]
  exact (fkRectConfigurationOfEdges_openEdges R _).symm




def fkRectInsertEdgeList (R : FKRectTorus) :
    Finset R.EdgeIndex → List R.EdgeIndex → Finset R.EdgeIndex
  | F, [] => F
  | F, e :: es => fkRectInsertEdgeList R (insert e F) es

theorem fkRectInsertEdgeList_eq_union_toFinset
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (es : List R.EdgeIndex) :
    fkRectInsertEdgeList R F es = F ∪ es.toFinset := by
  classical
  induction es generalizing F with
  | nil => simp [fkRectInsertEdgeList]
  | cons e es ih =>
      rw [fkRectInsertEdgeList, ih]
      ext a
      simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]
      tauto



noncomputable def fkRectWiredDualAddedEdgeList
    (R : FKRectTorus) (omega : R.Configuration) : List R.EdgeIndex :=
  (fkRectWiredDualAddedEdges R omega).toList

@[simp] theorem fkRectWiredDualAddedEdgeList_toFinset
    (R : FKRectTorus) (omega : R.Configuration) :
    (fkRectWiredDualAddedEdgeList R omega).toFinset =
      fkRectWiredDualAddedEdges R omega := by
  classical
  simp [fkRectWiredDualAddedEdgeList]

theorem fkRectInsert_wiredDualAddedEdgeList
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectInsertEdgeList R
        (fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega))
        (fkRectWiredDualAddedEdgeList R omega) =
      fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega) ∪
        fkRectWiredDualAddedEdges R omega := by
  rw [fkRectInsertEdgeList_eq_union_toFinset,
    fkRectWiredDualAddedEdgeList_toFinset]



theorem fkRectDual_forceCutClosed_eq_configurationOfInsertedEdgeList
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega) =
      fkRectConfigurationOfEdges R
        (fkRectInsertEdgeList R
          (fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega))
          (fkRectWiredDualAddedEdgeList R omega)) := by
  rw [fkRectInsert_wiredDualAddedEdgeList]
  exact fkRectDual_forceCutClosed_eq_configurationOfInsertedEdges R omega


def fkRectDualRightBoundaryEdge
    (R : FKRectTorus) (y : Fin R.height) : R.EdgeIndex :=
  (true, (fkRectRightColumn R, y))

theorem fkRectDualRightBoundaryEdge_mem_dualCutEdges
    (R : FKRectTorus) (y : Fin R.height) :
    fkRectDualRightBoundaryEdge R y ∈ fkRectDualCutEdges R := by
  rw [mem_fkRectDualCutEdges_iff]
  simp only [fkRectDualRightBoundaryEdge, fkRectDualEdgeToEdge, ↓reduceIte]
  rw [finitePeriodicSucc_fkRectRightColumn]
  rw [mem_fkRectTorusCutEdges_iff]
  exact Or.inr ⟨rfl, rfl⟩


def fkRectDualRightBoundaryEdgeList
    (R : FKRectTorus) : List R.EdgeIndex :=
  (List.finRange R.height).map (fkRectDualRightBoundaryEdge R)

theorem mem_fkRectDualRightBoundaryEdgeList
    (R : FKRectTorus) (e : R.EdgeIndex) :
    e ∈ fkRectDualRightBoundaryEdgeList R ↔
      ∃ y : Fin R.height, fkRectDualRightBoundaryEdge R y = e := by
  simp [fkRectDualRightBoundaryEdgeList]

theorem fkRectDualRightBoundaryEdgeList_subset_dualCutEdges
    (R : FKRectTorus) {e : R.EdgeIndex}
    (he : e ∈ fkRectDualRightBoundaryEdgeList R) :
    e ∈ fkRectDualCutEdges R := by
  obtain ⟨y, rfl⟩ := (mem_fkRectDualRightBoundaryEdgeList R e).1 he
  exact fkRectDualRightBoundaryEdge_mem_dualCutEdges R y



def fkRectWiredDualRightBoundaryAddedEdgeList
    (R : FKRectTorus) (omega : R.Configuration) : List R.EdgeIndex :=
  (fkRectDualRightBoundaryEdgeList R).filter
    (fun e => e ∈ fkRectWiredDualAddedEdges R omega)

theorem mem_fkRectWiredDualRightBoundaryAddedEdgeList
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex) :
    e ∈ fkRectWiredDualRightBoundaryAddedEdgeList R omega ↔
      e ∈ fkRectDualRightBoundaryEdgeList R ∧
        e ∈ fkRectWiredDualAddedEdges R omega := by
  classical
  simp [fkRectWiredDualRightBoundaryAddedEdgeList]



noncomputable def fkRectZeroTurnDualRightBoundaryContacts
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    Finset (Fin R.height) := by
  classical
  exact Finset.univ.filter fun y =>
    (fkRectRightColumn R, y) ∈
      (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C).support

theorem mem_fkRectZeroTurnDualRightBoundaryContacts
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (y : Fin R.height) :
    y ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C ↔
      (fkRectRightColumn R, y) ∈
        (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C).support := by
  classical
  simp [fkRectZeroTurnDualRightBoundaryContacts]



theorem fkRectZeroTurnDualRightBoundaryContacts_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    (fkRectZeroTurnDualRightBoundaryContacts R omega C).Nonempty := by
  have hwind : (fkRectWalkWinding R
      (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C)).1 ≠ 0 := by
    rw [fkRectZeroTurnRemainderDualBoundaryCycleWalk_winding]
    exact fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero R omega C
  obtain ⟨y, hy⟩ :=
    exists_fkRectRightBoundaryVertex_mem_support_of_winding R
      (fkRectDualConfigurationEquiv R omega)
      (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C) hwind
  exact ⟨y,
    (mem_fkRectZeroTurnDualRightBoundaryContacts R omega C y).2 hy⟩



def FKRectMergeInsertionOrder (R : FKRectTorus) :
    Finset R.EdgeIndex → List R.EdgeIndex → Prop
  | _, [] => True
  | F, e :: es =>
      e ∉ F ∧
        ¬ (fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R
            (fkRectConfigurationOfEdges R F))).Reachable
              (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
              (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) ∧
        FKRectMergeInsertionOrder R (insert e F) es



theorem fkRectBlackBoundaryPerm_insert_merge_partition
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hmerge : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (x : FKMedialBlackDart R.medialTorus) :
    (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R (insert e F)))).SameCycle
          (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) x ↔
      (fkMedialBlackBoundaryPerm
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))).SameCycle
            (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) x ∨
        (fkMedialBlackBoundaryPerm
          (fkRectConfigurationToMedialPairing R
            (fkRectConfigurationOfEdges R F))).SameCycle
              (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)) x := by
  rw [fkRectConfigurationToMedialPairing_insert R F e heF]
  exact fkMedialBlackBoundaryPerm_toggle_merge_partition
    (fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F))
    (fkRectMedialVertexOfEdge R e) hmerge x



theorem fkRectBlackBoundaryPerm_sameCycle_insertEdgeList_of_mergeOrder
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (es : List R.EdgeIndex)
    (horder : FKRectMergeInsertionOrder R F es)
    {x y : FKMedialBlackDart R.medialTorus}
    (hxy : (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).SameCycle x y) :
    (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R
          (fkRectInsertEdgeList R F es)))).SameCycle x y := by
  induction es generalizing F with
  | nil => simpa [fkRectInsertEdgeList]
  | cons e es ih =>
      rcases horder with ⟨heF, hmerge, htail⟩
      apply ih (insert e F) htail
      rw [fkRectConfigurationToMedialPairing_insert R F e heF]
      exact
        fkMedialBlackBoundaryPerm_toggle_sameCycle_mono_of_not_reachable
          (fkRectConfigurationToMedialPairing R
            (fkRectConfigurationOfEdges R F))
          (fkRectMedialVertexOfEdge R e) hmerge hxy



theorem fkRectMedialLoopGraph_reachable_insertEdgeList_of_mergeOrder
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (es : List R.EdgeIndex)
    (horder : FKRectMergeInsertionOrder R F es)
    {d e : FKMedialDart R.medialTorus}
    (hde : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable d e) :
    (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R
          (fkRectInsertEdgeList R F es)))).Reachable d e := by
  induction es generalizing F with
  | nil => simpa [fkRectInsertEdgeList]
  | cons a es ih =>
      rcases horder with ⟨haF, hmerge, htail⟩
      apply ih (insert a F) htail
      rw [fkRectConfigurationToMedialPairing_insert R F a haF]
      exact fkMedialLoopGraph_toggle_reachable_mono_of_not_reachable
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))
        (fkRectMedialVertexOfEdge R a) hmerge hde

end

end StatMech.FrontierD
