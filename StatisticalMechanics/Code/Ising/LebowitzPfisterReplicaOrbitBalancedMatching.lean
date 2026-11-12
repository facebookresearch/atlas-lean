/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Combinatorics.Hall.Basic
import Code.Ising.LebowitzPfisterReplicaSameProfileCounterexample















open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaBalancedMatchingDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _





def LPReplicaProfileOrbitLabelReallocates
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    {m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (M : LPReplicaProfileOrbitLabel G sites q n) : Prop :=
  forall e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
    ∃ R T : Finset (Fin (q e.1)),
      R ⊆ (L e).1 ∧
      T ⊆ Finset.univ \ (L e).1 ∧
      (M e).1 = ((L e).1 \ R) ∪ T



theorem lpReplicaProfileOrbitLabelReallocates_all
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    {m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (M : LPReplicaProfileOrbitLabel G sites q n) :
    LPReplicaProfileOrbitLabelReallocates G sites q L M := by
  intro e
  let R := (L e).1 \ (M e).1
  let T := (M e).1 \ (L e).1
  refine ⟨R, T, Finset.sdiff_subset, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨Finset.mem_univ _, hx.2⟩
  · ext x
    simp only [R, T, Finset.mem_union, Finset.mem_sdiff]
    tauto

abbrev LPReplicaOffdiagDecoratedSource
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  LPReplicaDecoratedOrbitAtom G sites ∅
    (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1) q

abbrev LPReplicaOffdiagDecoratedTarget
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q ⊕
    LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q

@[simp] theorem lpReplicaDecoratedOrbitAtomOfRowGate_profile
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    (lpReplicaDecoratedOrbitAtomOfRowGate
      G sites m q tag A B hm hgate L).1.1.1 = m := rfl

@[simp] theorem lpReplicaDecoratedOrbitAtomOfRowGate_orbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    (lpReplicaDecoratedOrbitAtomOfRowGate
      G sites m q tag A B hm hgate L).2.2 = L := rfl

@[simp] theorem lpReplicaDecoratedOrbitAtomOfRowGate_row0
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    (lpReplicaDecoratedOrbitAtomOfRowGate
      G sites m q tag A B hm hgate L).2.1.1 =
        lpReplicaRowCopies G sites m tag false := rfl

theorem lpReplicaDecoratedOrbitAtom_cast_profile
    (G : SimpleGraph V) (sites : I -> V)
    (A D E : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (h : D = E) (x : LPReplicaDecoratedOrbitAtom G sites A D q) :
    (cast (congrArg
      (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) h) x).1.1.1 =
        x.1.1.1 := by
  subst E
  rfl

theorem lpReplicaDecoratedOrbitAtom_cast_orbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (A D E : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (h : D = E) (x : LPReplicaDecoratedOrbitAtom G sites A D q) :
    HEq (cast (congrArg
      (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) h) x).2.2
      x.2.2 := by
  subst E
  rfl

theorem lpReplicaDecoratedOrbitAtom_cast_row0
    (G : SimpleGraph V) (sites : I -> V)
    (A D E : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (h : D = E) (x : LPReplicaDecoratedOrbitAtom G sites A D q) :
    HEq (cast (congrArg
      (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) h) x).2.1.1
      x.2.1.1 := by
  subst E
  rfl

@[simp] theorem lpReplicaDecoratedOrbitAtomOfBalancedSelector_profile
    (G : SimpleGraph V) (sites : I -> V)
    (Si Sj T : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q) :
    (lpReplicaDecoratedOrbitAtomOfBalancedSelector
      G sites Si Sj T q s).1.1.1 = s.profile := rfl

@[simp] theorem lpReplicaDecoratedOrbitAtomOfBalancedSelector_orbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (Si Sj T : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q) :
    (lpReplicaDecoratedOrbitAtomOfBalancedSelector
      G sites Si Sj T q s).2.2 = s.orbitLabel := rfl

@[simp] theorem lpReplicaDecoratedOrbitAtomOfBalancedSelector_row0
    (G : SimpleGraph V) (sites : I -> V)
    (Si Sj T : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q) :
    (lpReplicaDecoratedOrbitAtomOfBalancedSelector
      G sites Si Sj T q s).2.1.1 =
      lpReplicaRowCopies G sites s.profile
        (lpReplicaToggleRows G sites s.profile s.selector s.tag) false := rfl



def LPReplicaOffdiagBalancedOutput
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) : Prop :=
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  (∃ s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q,
      y = Sum.inl
        (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
          G sites i j q s)) ∨
    (∃ s : LPReplicaBalancedSelector G sites
      (Sj ∆ Si ∆ T) (Si ∆ T) q,
      y = Sum.inr
        (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
          G sites j i q s))




def LPReplicaOffdiagBalancedMatch
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) : Prop :=
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  (∃ s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q,
      LPReplicaProfileOrbitLabelReallocates G sites q z.2.2 s.orbitLabel ∧
      y = Sum.inl
        (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
          G sites i j q s)) ∨
    (∃ s : LPReplicaBalancedSelector G sites
      (Sj ∆ Si ∆ T) (Si ∆ T) q,
      LPReplicaProfileOrbitLabelReallocates G sites q z.2.2 s.orbitLabel ∧
      y = Sum.inr
        (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
          G sites j i q s))

theorem lpReplicaOffdiagBalancedMatch_iff_output
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    LPReplicaOffdiagBalancedMatch G sites i j q z y ↔
      LPReplicaOffdiagBalancedOutput G sites i j q y := by
  dsimp only [LPReplicaOffdiagBalancedMatch,
    LPReplicaOffdiagBalancedOutput]
  constructor
  · rintro (⟨s, _, hy⟩ | ⟨s, _, hy⟩)
    · exact Or.inl ⟨s, hy⟩
    · exact Or.inr ⟨s, hy⟩
  · rintro (⟨s, hy⟩ | ⟨s, hy⟩)
    · exact Or.inl ⟨s,
        lpReplicaProfileOrbitLabelReallocates_all
          G sites q z.2.2 s.orbitLabel, hy⟩
    · exact Or.inr ⟨s,
        lpReplicaProfileOrbitLabelReallocates_all
          G sites q z.2.2 s.orbitLabel, hy⟩


noncomputable def lpReplicaOffdiagBalancedNeighbors
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact Finset.univ.filter fun y =>
    LPReplicaOffdiagBalancedMatch G sites i j q z y



noncomputable def lpReplicaOffdiagBalancedOutputs
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact Finset.univ.filter
    (LPReplicaOffdiagBalancedOutput G sites i j q)



noncomputable def lpReplicaOffdiagBalancedLeftOutputs
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  exact Finset.univ.filter fun y =>
    ∃ s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q,
      y = Sum.inl
        (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
          G sites i j q s)


noncomputable def lpReplicaOffdiagBalancedRightOutputs
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  exact Finset.univ.filter fun y =>
    ∃ s : LPReplicaBalancedSelector G sites
      (Sj ∆ Si ∆ T) (Si ∆ T) q,
      y = Sum.inr
        (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
          G sites j i q s)


def lpReplicaOffdiagDecoratedTargetProfile
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOffdiagDecoratedTarget G sites i j q ->
      (lpReplicaCurrentGraph G sites).edgeFinset -> Nat
  | Sum.inl y => y.1.1.1
  | Sum.inr y => y.1.1.1


noncomputable def lpReplicaOffdiagDecoratedSourcesAtProfile
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact Finset.univ.filter fun z => z.1.1.1 = m


noncomputable def lpReplicaOffdiagBalancedLeftOutputsAtProfile
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact (lpReplicaOffdiagBalancedLeftOutputs G sites i j q).filter fun y =>
    lpReplicaOffdiagDecoratedTargetProfile G sites i j q y = m


noncomputable def lpReplicaOffdiagBalancedRightOutputsAtProfile
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact (lpReplicaOffdiagBalancedRightOutputs G sites i j q).filter fun y =>
    lpReplicaOffdiagDecoratedTargetProfile G sites i j q y = m



noncomputable def lpReplicaOffdiagBalancedRelevantProfiles
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) := by
  classical
  exact ((Finset.univ : Finset
        (LPReplicaOffdiagDecoratedSource G sites i j q)).image
      (fun z => z.1.1.1)) ∪
    (lpReplicaOffdiagBalancedLeftOutputs G sites i j q).image
      (lpReplicaOffdiagDecoratedTargetProfile G sites i j q) ∪
    (lpReplicaOffdiagBalancedRightOutputs G sites i j q).image
      (lpReplicaOffdiagDecoratedTargetProfile G sites i j q)

theorem lpReplicaOffdiagDecoratedSource_card_eq_sum_profileFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) =
      ∑ m ∈ lpReplicaOffdiagBalancedRelevantProfiles G sites i j q,
        (lpReplicaOffdiagDecoratedSourcesAtProfile
          G sites i j q m).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagDecoratedSourcesAtProfile] using
    Finset.card_eq_sum_card_fiberwise (by
    intro z hz
    unfold lpReplicaOffdiagBalancedRelevantProfiles
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inl (Finset.mem_image.mpr ⟨z, hz, rfl⟩)))))

theorem lpReplicaOffdiagBalancedLeftOutputs_card_eq_sum_profileFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagBalancedLeftOutputs G sites i j q).card =
      ∑ m ∈ lpReplicaOffdiagBalancedRelevantProfiles G sites i j q,
        (lpReplicaOffdiagBalancedLeftOutputsAtProfile
          G sites i j q m).card := by
  classical
  simpa only [lpReplicaOffdiagBalancedLeftOutputsAtProfile] using
    Finset.card_eq_sum_card_fiberwise (by
    intro y hy
    unfold lpReplicaOffdiagBalancedRelevantProfiles
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inr (Finset.mem_image.mpr ⟨y, hy, rfl⟩)))))

theorem lpReplicaOffdiagBalancedRightOutputs_card_eq_sum_profileFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagBalancedRightOutputs G sites i j q).card =
      ∑ m ∈ lpReplicaOffdiagBalancedRelevantProfiles G sites i j q,
        (lpReplicaOffdiagBalancedRightOutputsAtProfile
          G sites i j q m).card := by
  classical
  simpa only [lpReplicaOffdiagBalancedRightOutputsAtProfile] using
    Finset.card_eq_sum_card_fiberwise (by
    intro y hy
    unfold lpReplicaOffdiagBalancedRelevantProfiles
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩)))


noncomputable def lpReplicaOffdiagBalancedBranchOutputs
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact lpReplicaOffdiagBalancedLeftOutputs G sites i j q ∪
    lpReplicaOffdiagBalancedRightOutputs G sites i j q

theorem lpReplicaOffdiagBalancedOutputs_eq_branch_union
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaOffdiagBalancedOutputs G sites i j q =
      lpReplicaOffdiagBalancedBranchOutputs G sites i j q := by
  classical
  ext y
  simp only [lpReplicaOffdiagBalancedOutputs,
    lpReplicaOffdiagBalancedBranchOutputs,
    lpReplicaOffdiagBalancedLeftOutputs,
    lpReplicaOffdiagBalancedRightOutputs,
    LPReplicaOffdiagBalancedOutput, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_union]

theorem lpReplicaOffdiagBalancedBranchOutputs_disjoint
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Disjoint
      (lpReplicaOffdiagBalancedLeftOutputs G sites i j q)
      (lpReplicaOffdiagBalancedRightOutputs G sites i j q) := by
  classical
  rw [Finset.disjoint_left]
  intro y hyLeft hyRight
  simp only [lpReplicaOffdiagBalancedLeftOutputs,
    lpReplicaOffdiagBalancedRightOutputs, Finset.mem_filter,
    Finset.mem_univ, true_and] at hyLeft hyRight
  obtain ⟨s, rfl⟩ := hyLeft
  obtain ⟨t, ht⟩ := hyRight
  exact Sum.inl_ne_inr ht



theorem lpReplicaOffdiagBalancedOutputs_card_eq_branch_sum
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagBalancedOutputs G sites i j q).card =
      (lpReplicaOffdiagBalancedLeftOutputs G sites i j q).card +
        (lpReplicaOffdiagBalancedRightOutputs G sites i j q).card := by
  classical
  rw [lpReplicaOffdiagBalancedOutputs_eq_branch_union]
  unfold lpReplicaOffdiagBalancedBranchOutputs
  rw [
    Finset.card_union_of_disjoint
      (lpReplicaOffdiagBalancedBranchOutputs_disjoint G sites i j q)]


noncomputable def LPReplicaOffdiagBalancedHall
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop := by
  classical
  exact forall S : Finset (LPReplicaOffdiagDecoratedSource G sites i j q),
    S.card <= (S.biUnion
      (lpReplicaOffdiagBalancedNeighbors G sites i j q)).card



theorem lpReplicaOffdiagDecoratedOrbitInjection_of_balancedHall
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hHall : LPReplicaOffdiagBalancedHall G sites i j q) :
    LPReplicaOffdiagDecoratedOrbitInjection G sites i j q := by
  classical
  obtain ⟨move, hmove, _⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (lpReplicaOffdiagBalancedNeighbors G sites i j q)).mp (by
        simpa only [LPReplicaOffdiagBalancedHall] using hHall)
  exact ⟨move, hmove⟩




theorem lpReplicaOffdiagBalancedHall_of_outputCard
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card
        (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagBalancedOutputs G sites i j q).card) :
    LPReplicaOffdiagBalancedHall G sites i j q := by
  classical
  intro S
  by_cases hS : S = ∅
  · simp [hS]
  let good := lpReplicaOffdiagBalancedOutputs G sites i j q
  have hneighbors (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
      lpReplicaOffdiagBalancedNeighbors G sites i j q z = good := by
    ext y
    simp only [lpReplicaOffdiagBalancedNeighbors, good,
      lpReplicaOffdiagBalancedOutputs,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact lpReplicaOffdiagBalancedMatch_iff_output G sites i j q z y
  have hnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  have hunion : S.biUnion
      (lpReplicaOffdiagBalancedNeighbors G sites i j q) = good := by
    ext y
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨z, hz, hy⟩
      rw [hneighbors z] at hy
      exact hy
    · intro hy
      obtain ⟨z, hz⟩ := hnonempty
      exact ⟨z, hz, by rwa [hneighbors z]⟩
  rw [hunion]
  calc
    S.card <= Fintype.card
        (LPReplicaOffdiagDecoratedSource G sites i j q) := by
      simpa only [Finset.card_univ] using
        Finset.card_le_card (Finset.subset_univ S)
    _ <= good.card := by simpa only [good] using hcard



theorem lpReplicaOffdiagOrbitAtomCardInequality_of_balancedOutputCard
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card
        (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagBalancedOutputs G sites i j q).card) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  apply lpReplicaOffdiagOrbitAtomCardInequality_of_decoratedInjection
  exact lpReplicaOffdiagDecoratedOrbitInjection_of_balancedHall
    G sites i j q
      (lpReplicaOffdiagBalancedHall_of_outputCard
        G sites i j q hcard)



theorem lpReplicaOffdiagOrbitAtomCardInequality_of_balancedBranchOutputCard
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card
        (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagBalancedLeftOutputs G sites i j q).card +
        (lpReplicaOffdiagBalancedRightOutputs G sites i j q).card) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  apply lpReplicaOffdiagOrbitAtomCardInequality_of_balancedOutputCard
  rwa [lpReplicaOffdiagBalancedOutputs_card_eq_branch_sum]




theorem lpReplicaOffdiagOrbitAtomCardInequality_of_balancedProfileFiberCards
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : ∀ m ∈
        lpReplicaOffdiagBalancedRelevantProfiles G sites i j q,
      (lpReplicaOffdiagDecoratedSourcesAtProfile
          G sites i j q m).card <=
        (lpReplicaOffdiagBalancedLeftOutputsAtProfile
            G sites i j q m).card +
          (lpReplicaOffdiagBalancedRightOutputsAtProfile
            G sites i j q m).card) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  apply lpReplicaOffdiagOrbitAtomCardInequality_of_balancedBranchOutputCard
  rw [lpReplicaOffdiagDecoratedSource_card_eq_sum_profileFibers,
    lpReplicaOffdiagBalancedLeftOutputs_card_eq_sum_profileFibers,
    lpReplicaOffdiagBalancedRightOutputs_card_eq_sum_profileFibers,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum hcard

end

end StatMech.Ising
