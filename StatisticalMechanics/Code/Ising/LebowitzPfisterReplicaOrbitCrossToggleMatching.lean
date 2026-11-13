/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots
import Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching













open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaCrossToggleMatchingDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


noncomputable def lpReplicaOffdiagDecoratedSourceSlotState
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    LPReplicaOrbitFourColorSlotState G sites q :=
  lpReplicaOrientedFourColorSlotState G sites ∅
    (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1) q
    (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q z)


theorem lpReplicaOffdiagDecoratedSourceSlotState_injective
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Injective
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q) :=
  (lpReplicaOrientedFourColorSlotState_injective G sites ∅
    (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1) q).comp
    (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q).injective


noncomputable def lpReplicaOffdiagDecoratedTargetBranchedSlotState
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOffdiagDecoratedTarget G sites i j q ->
      Bool × LPReplicaOrbitFourColorSlotState G sites q
  | Sum.inl y => (false,
      lpReplicaOrientedFourColorSlotState G sites
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites
          (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q y))

  | Sum.inr y => (true,
      lpReplicaOrientedFourColorSlotState G sites
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites
          (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q y))



theorem lpReplicaOffdiagDecoratedTargetBranchedSlotState_injective
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Injective
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q) := by
  intro y w h
  rcases y with y | y <;> rcases w with w | w
  · apply congrArg Sum.inl
    apply (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q).injective
    apply lpReplicaOrientedFourColorSlotState_injective
    exact congrArg Prod.snd h
  · have hbranch := congrArg Prod.fst h
    exfalso
    change false = true at hbranch
    exact Bool.false_ne_true hbranch
  · have hbranch := congrArg Prod.fst h
    exfalso
    change true = false at hbranch
    exact Bool.false_ne_true hbranch.symm
  · apply congrArg Sum.inr
    apply (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q).injective
    apply lpReplicaOrientedFourColorSlotState_injective
    exact congrArg Prod.snd h


noncomputable def lpReplicaOffdiagDecoratedSourceCrossTrace
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    LPReplicaOrbitFourColorSlotState G sites q :=
  lpReplicaOrbitFourColorSlotCrossNormalize G sites q
    (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)


noncomputable def lpReplicaOffdiagDecoratedTargetCrossTrace
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    LPReplicaOrbitFourColorSlotState G sites q :=
  lpReplicaOrbitFourColorSlotCrossNormalize G sites q
    (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2



def LPReplicaOffdiagCrossToggleMaskRelated
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) : Prop :=
  y ∈ lpReplicaOffdiagBalancedOutputs G sites i j q ∧
    ∃ P : Finset (LPReplicaOrbitCommonSlot G sites q),
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q y).2 =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q P
          (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)



theorem lpReplicaOffdiagCrossToggleMaskRelated_iff_crossTrace
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    LPReplicaOffdiagCrossToggleMaskRelated G sites i j q z y ↔
      y ∈ lpReplicaOffdiagBalancedOutputs G sites i j q ∧
        lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y =
          lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z := by
  unfold LPReplicaOffdiagCrossToggleMaskRelated
    lpReplicaOffdiagDecoratedTargetCrossTrace
    lpReplicaOffdiagDecoratedSourceCrossTrace
  rw [exists_crossToggle_eq_iff_crossNormalize_eq]


noncomputable def lpReplicaOffdiagCrossToggleMaskNeighbors
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact Finset.univ.filter fun y =>
    LPReplicaOffdiagCrossToggleMaskRelated G sites i j q z y


noncomputable def LPReplicaOffdiagCrossToggleMaskHall
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop := by
  classical
  exact forall S : Finset (LPReplicaOffdiagDecoratedSource G sites i j q),
    S.card <= (S.biUnion
      (lpReplicaOffdiagCrossToggleMaskNeighbors G sites i j q)).card


noncomputable def lpReplicaOffdiagDecoratedSourceCrossTraceFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact Finset.univ.filter fun z =>
    lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z = u


noncomputable def lpReplicaOffdiagBalancedOutputCrossTraceFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact (lpReplicaOffdiagBalancedOutputs G sites i j q).filter fun y =>
    lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y = u


noncomputable def lpReplicaOffdiagDecoratedSourceCrossTraceMasks
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (Finset (LPReplicaOrbitCommonSlot G sites q)) := by
  classical
  exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
    G sites i j q u).image fun z =>
      lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)



noncomputable def lpReplicaOffdiagBalancedOutputCrossTraceBranchedMasks
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (Bool × Finset (LPReplicaOrbitCommonSlot G sites q)) := by
  classical
  exact (lpReplicaOffdiagBalancedOutputCrossTraceFiber
    G sites i j q u).image fun y =>
      ((lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).1,
        lpReplicaOrbitFourColorSlotRowMask G sites q
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2)



theorem lpReplicaOffdiagDecoratedSourceRowMask_injOn_crossTraceFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Set.InjOn (fun z : LPReplicaOffdiagDecoratedSource G sites i j q =>
      lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z))
      (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
        G sites i j q u) := by
  classical
  intro z hz w hw hmask
  simp only [Finset.mem_coe] at hz hw
  apply lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q
  let sz := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z
  let sw := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w
  have htracez : lpReplicaOrbitFourColorSlotCrossNormalize G sites q sz = u := by
    simpa only [lpReplicaOffdiagDecoratedSourceCrossTraceFiber,
      Finset.mem_filter, Finset.mem_univ, true_and,
      lpReplicaOffdiagDecoratedSourceCrossTrace] using hz
  have htracew : lpReplicaOrbitFourColorSlotCrossNormalize G sites q sw = u := by
    simpa only [lpReplicaOffdiagDecoratedSourceCrossTraceFiber,
      Finset.mem_filter, Finset.mem_univ, true_and,
      lpReplicaOffdiagDecoratedSourceCrossTrace] using hw
  change lpReplicaOrbitFourColorSlotRowMask G sites q sz =
    lpReplicaOrbitFourColorSlotRowMask G sites q sw at hmask
  calc
    sz = lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitFourColorSlotRowMask G sites q sz)
        (lpReplicaOrbitFourColorSlotCrossNormalize G sites q sz) :=
      (lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize
        G sites q sz).symm
    _ = lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitFourColorSlotRowMask G sites q sw)
        (lpReplicaOrbitFourColorSlotCrossNormalize G sites q sw) := by
      rw [hmask, htracez, htracew]
    _ = sw := lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize
      G sites q sw



theorem lpReplicaOffdiagDecoratedTargetBranchedRowMask_injOn_crossTraceFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Set.InjOn (fun y : LPReplicaOffdiagDecoratedTarget G sites i j q =>
      ((lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).1,
        lpReplicaOrbitFourColorSlotRowMask G sites q
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2))
      (lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u) := by
  classical
  intro y hy w hw hmask
  simp only [Finset.mem_coe] at hy hw
  have hbranch := congrArg (fun p : Bool ×
      Finset (LPReplicaOrbitCommonSlot G sites q) => p.1) hmask
  let sy := (lpReplicaOffdiagDecoratedTargetBranchedSlotState
    G sites i j q y).2
  let sw := (lpReplicaOffdiagDecoratedTargetBranchedSlotState
    G sites i j q w).2
  have htracey : lpReplicaOrbitFourColorSlotCrossNormalize G sites q sy = u := by
    have h := (Finset.mem_filter.mp hy).2
    exact h
  have htracew : lpReplicaOrbitFourColorSlotCrossNormalize G sites q sw = u := by
    have h := (Finset.mem_filter.mp hw).2
    exact h
  have hrow := congrArg (fun p : Bool ×
      Finset (LPReplicaOrbitCommonSlot G sites q) => p.2) hmask
  change lpReplicaOrbitFourColorSlotRowMask G sites q sy =
    lpReplicaOrbitFourColorSlotRowMask G sites q sw at hrow
  have hstate : sy = sw := by
    calc
      sy = lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitFourColorSlotRowMask G sites q sy)
          (lpReplicaOrbitFourColorSlotCrossNormalize G sites q sy) :=
        (lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize
          G sites q sy).symm
      _ = lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitFourColorSlotRowMask G sites q sw)
          (lpReplicaOrbitFourColorSlotCrossNormalize G sites q sw) := by
        rw [hrow, htracey, htracew]
      _ = sw := lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize
        G sites q sw
  apply lpReplicaOffdiagDecoratedTargetBranchedSlotState_injective
    G sites i j q
  exact Prod.ext hbranch hstate


theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiber_card_eq_masks
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card =
      (lpReplicaOffdiagDecoratedSourceCrossTraceMasks
        G sites i j q u).card := by
  classical
  symm
  exact Finset.card_image_iff.mpr
    (lpReplicaOffdiagDecoratedSourceRowMask_injOn_crossTraceFiber
      G sites i j q u)



theorem lpReplicaOffdiagBalancedOutputCrossTraceFiber_card_eq_branchedMasks
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card =
      (lpReplicaOffdiagBalancedOutputCrossTraceBranchedMasks
        G sites i j q u).card := by
  classical
  symm
  exact Finset.card_image_iff.mpr
    (lpReplicaOffdiagDecoratedTargetBranchedRowMask_injOn_crossTraceFiber
      G sites i j q u)




theorem lpReplica_half_ne_doubledBoundary_of_nonempty
    (X D : Finset (LPReplicaCurrentVertex V))
    (hD : D = X ∆ X.map lpReplicaCurrentReflect.toEmbedding)
    (hDne : D.Nonempty) : X ≠ D := by
  intro hXD
  have hself : X = X ∆ X.map lpReplicaCurrentReflect.toEmbedding :=
    hXD.trans hD
  have hreflectEmpty :
      X.map lpReplicaCurrentReflect.toEmbedding = ∅ := by
    have hcancel : (∅ : Finset (LPReplicaCurrentVertex V)) =
        X.map lpReplicaCurrentReflect.toEmbedding := by
      calc
        ∅ = X ∆ X := by simp
        _ = X ∆ (X ∆ X.map lpReplicaCurrentReflect.toEmbedding) :=
          congrArg (fun Y => X ∆ Y) hself
        _ = X.map lpReplicaCurrentReflect.toEmbedding :=
          symmDiff_symmDiff_cancel_left _ _
    exact hcancel.symm
  have hXempty : X = ∅ := Finset.map_eq_empty.mp hreflectEmpty
  have hDempty : D = ∅ := by
    rw [hD, hXempty]
    simp
  exact Finset.nonempty_iff_ne_empty.mp hDne hDempty



theorem lpReplicaDecoratedSourceCanonicalHalfBranch_not_directTarget
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    match lpReplicaDecoratedSourceCanonicalHalfBranch
        G sites hsite hij q z with
    | Sum.inl b => b.1 ≠ Sj ∆ T
    | Sum.inr b => b.1 ≠ Si ∆ T := by
  dsimp only
  let branch := lpReplicaDecoratedSourceCanonicalHalfBranch
    G sites hsite hij q z
  change match branch with
    | Sum.inl b => b.1 ≠
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1
    | Sum.inr b => b.1 ≠
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1
  rcases hbranch : branch with left | right
  · change left.1 ≠
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1
    apply lpReplica_half_ne_doubledBoundary_of_nonempty
      left.1
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      left.2.2
    refine ⟨(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V), ?_⟩
    simp [lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff]
  · change right.1 ≠
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1
    apply lpReplica_half_ne_doubledBoundary_of_nonempty
      right.1
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      right.2.2
    refine ⟨(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V), ?_⟩
    simp [lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff]



noncomputable def lpReplicaDecoratedSourceCanonicalHalfSlotMask
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    Finset (LPReplicaOrbitCommonSlot G sites q) :=
  lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2
    (lpReplicaDecoratedSourceCanonicalHalfSelector
      G sites i j q z).selector


noncomputable def lpReplicaDecoratedSourceCanonicalHalfBranchBit
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) : Bool :=
  match lpReplicaDecoratedSourceCanonicalHalfBranch
      G sites hsite hij q z with
  | Sum.inl _ => false
  | Sum.inr _ => true




noncomputable def lpReplicaDecoratedSourceCanonicalHalfCandidate
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    Bool × LPReplicaOrbitFourColorSlotState G sites q :=
  (lpReplicaDecoratedSourceCanonicalHalfBranchBit
      G sites hsite hij q z,
    lpReplicaOrbitFourColorSlotCrossToggle G sites q
      (lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q z)
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z))




theorem lpReplicaDecoratedSourceCanonicalHalfCandidate_allocation
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    (lpReplicaDecoratedSourceCanonicalHalfCandidate
        G sites hsite hij q z).2.allocation =
      fun e => ((lpReplicaProfileOrbitLabelPartialReflectCopies G sites q
        z.1.1.1 z.1.1.2
        (lpReplicaDecoratedSourceCanonicalHalfSelector
          G sites i j q z).selector z.2.2) e).1 := by
  unfold lpReplicaDecoratedSourceCanonicalHalfCandidate
    lpReplicaDecoratedSourceCanonicalHalfSlotMask
    lpReplicaOffdiagDecoratedSourceSlotState
    lpReplicaOrientedFourColorSlotState
  exact lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_allocation
    G sites q z.1.1.1 z.1.1.2 z.2.2
      (lpReplicaDecoratedSourceCanonicalHalfSelector
        G sites i j q z).selector
      (lpReplicaOrientedFourColorTag G sites ∅
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q z))




theorem lpReplicaDecoratedSourceCanonicalHalfCandidate_color
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    (lpReplicaDecoratedSourceCanonicalHalfCandidate
        G sites hsite hij q z).2.color =
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1
        z.1.1.2 z.2.2
        (lpReplicaToggleRows G sites z.1.1.1
          (lpReplicaDecoratedSourceCanonicalHalfSelector
            G sites i j q z).selector
          (lpReplicaOrientedFourColorTag G sites ∅
            (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
              lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) q
            (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅
              (lpMatchingSeamSource
                  (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
                lpMatchingSeamSource
                  (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
                lpMatchingGhostSource
                  (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                  lpReplicaCurrentGhost1) q z)))).color := by
  unfold lpReplicaDecoratedSourceCanonicalHalfCandidate
    lpReplicaDecoratedSourceCanonicalHalfSlotMask
    lpReplicaOffdiagDecoratedSourceSlotState
    lpReplicaOrientedFourColorSlotState
  exact lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_color
    G sites q z.1.1.1 z.1.1.2 z.2.2
      (lpReplicaDecoratedSourceCanonicalHalfSelector
        G sites i j q z).selector
      (lpReplicaOrientedFourColorTag G sites ∅
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q z))

set_option maxHeartbeats 800000 in



theorem lpReplicaDecoratedSourceCanonicalHalfCandidate_eq_iff
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z w : LPReplicaOffdiagDecoratedSource G sites i j q) :
    lpReplicaDecoratedSourceCanonicalHalfCandidate
        G sites hsite hij q z =
      lpReplicaDecoratedSourceCanonicalHalfCandidate
        G sites hsite hij q w ↔
      lpReplicaDecoratedSourceCanonicalHalfBranchBit
          G sites hsite hij q z =
        lpReplicaDecoratedSourceCanonicalHalfBranchBit
          G sites hsite hij q w ∧
      lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z =
        lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q w ∧
      lpReplicaOrbitFourColorSlotRowMask G sites q
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) ∆
          lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q z =
        lpReplicaOrbitFourColorSlotRowMask G sites q
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w) ∆
          lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q w := by
  unfold lpReplicaDecoratedSourceCanonicalHalfCandidate
  constructor
  · intro h
    refine ⟨congrArg Prod.fst h, ?_⟩
    have hstate := congrArg Prod.snd h
    exact (lpReplicaOrbitFourColorSlotCrossToggle_eq_iff G sites q
      (lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q z)
      (lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q w)
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w)).mp hstate
  · rintro ⟨hbranch, htrace, hrow⟩
    apply Prod.ext hbranch
    exact (lpReplicaOrbitFourColorSlotCrossToggle_eq_iff G sites q
      (lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q z)
      (lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q w)
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w)).mpr
        ⟨htrace, hrow⟩


theorem isEmpty_lpReplicaOrbitCommonSlot_zero
    (G : SimpleGraph V) (sites : I -> V) :
    IsEmpty (LPReplicaOrbitCommonSlot G sites (fun _ => 0)) := by
  constructor
  intro x
  rcases x with ⟨fixed, k⟩ | ⟨strict, k⟩
  · have hk : (fun _ : (lpReplicaCurrentGraph G sites).edgeFinset => 0)
        fixed.1 / 2 = 0 := by simp
    exact Fin.elim0 (Fin.cast hk k)
  · exact Fin.elim0 k




theorem isEmpty_lpReplicaOffdiagDecoratedSource_zero
    (G : SimpleGraph V) (sites : I -> V) (i j : I) :
    IsEmpty (LPReplicaOffdiagDecoratedSource G sites i j (fun _ => 0)) := by
  constructor
  intro z
  let d := lpReplicaDecoratedSourceRowGateData
    G sites i j (fun _ => 0) z
  have hmle : z.1.1.1 <= (fun _ => 0) :=
    lpReplicaProfile_le_of_symmetrizedProfile_eq G sites z.1.1.2
  have hmzero : z.1.1.1 = (fun _ => 0) := by
    funext e
    exact Nat.le_zero.mp (hmle e)
  have hcopies : lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false = ∅ := by
    ext c
    have hc : False := by
      rcases c with ⟨e, k⟩
      have hk : z.1.1.1 e = 0 := congrFun hmzero e
      exact Fin.elim0 (Fin.cast hk k)
    exact False.elim hc
  have hboundary :
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 = ∅ := by
    rw [← d.2.2.2.2.1, hcopies]
    simp [StatMech.Sharpness.RandomCurrent.sources,
      StatMech.Sharpness.RandomCurrent.degK]
  have hghost : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := by
    simp [lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff]
  rw [hboundary] at hghost
  simp at hghost



theorem lpReplicaOffdiagCrossToggleMaskHall_zero
    (G : SimpleGraph V) (sites : I -> V) (i j : I) :
    LPReplicaOffdiagCrossToggleMaskHall G sites i j (fun _ => 0) := by
  classical
  unfold LPReplicaOffdiagCrossToggleMaskHall
  intro S
  have hS : S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z _
    exact (isEmpty_lpReplicaOffdiagDecoratedSource_zero G sites i j).false z
  simp [hS]


theorem randomCurrent_sources_subset_endpointSupport
    {E W : Type*} [Fintype E] [DecidableEq E]
    [Fintype W] [DecidableEq W]
    (ends : E -> Sym2 W) (K : Finset E) :
    StatMech.Sharpness.RandomCurrent.sources ends K ⊆
      K.biUnion fun e => (ends e).toFinset := by
  classical
  intro x hx
  rw [StatMech.Sharpness.RandomCurrent.mem_sources] at hx
  have hne : StatMech.Sharpness.RandomCurrent.degK ends K x ≠ 0 := by
    rcases hx with ⟨n, hn⟩
    omega
  have hfilter : (K.filter fun e => x ∈ ends e).Nonempty := by
    rw [← Finset.card_pos]
    exact Nat.pos_of_ne_zero hne
  obtain ⟨e, he⟩ := hfilter
  obtain ⟨heK, hxe⟩ := Finset.mem_filter.mp he
  apply Finset.mem_biUnion.mpr
  exact ⟨e, heK, Sym2.mem_toFinset.mpr hxe⟩


theorem card_randomCurrent_sources_le_two_mul_card
    {E W : Type*} [Fintype E] [DecidableEq E]
    [Fintype W] [DecidableEq W]
    (ends : E -> Sym2 W) (K : Finset E) :
    (StatMech.Sharpness.RandomCurrent.sources ends K).card <= 2 * K.card := by
  classical
  let support : Finset W := K.biUnion fun e => (ends e).toFinset
  calc
    _ <= support.card := Finset.card_le_card
      (randomCurrent_sources_subset_endpointSupport ends K)
    _ <= ∑ e ∈ K, (ends e).toFinset.card := Finset.card_biUnion_le
    _ <= ∑ _e ∈ K, 2 := by
      apply Finset.sum_le_sum
      intro e _
      rw [Sym2.card_toFinset]
      split <;> omega
    _ = 2 * K.card := by simp [Nat.mul_comm]



omit [Fintype V] [Fintype I] [DecidableEq I] in
theorem card_lpReplica_offdiagSource
    (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j) :
    (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1).card = 6 := by
  have hsij : sites i ≠ sites j := hsite.ne hij
  have hi : ({lpReplicaCurrentLeft sites i} :
      Finset (LPReplicaCurrentVertex V)) ∆
        {lpReplicaCurrentRight sites i} =
      {lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]
  have hj : ({lpReplicaCurrentLeft sites j} :
      Finset (LPReplicaCurrentVertex V)) ∆
        {lpReplicaCurrentRight sites j} =
      {lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]
  have hg : ({(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)} :
      Finset (LPReplicaCurrentVertex V)) ∆ {lpReplicaCurrentGhost1} =
      {(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V),
        lpReplicaCurrentGhost1} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]
  have hdij : Disjoint
      ({lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} :
        Finset (LPReplicaCurrentVertex V))
      {lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j} := by
    simp [lpReplicaCurrentLeft, lpReplicaCurrentRight, hsij.symm]
  have hdghost : Disjoint
      (({lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} :
          Finset (LPReplicaCurrentVertex V)) ∪
        {lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j})
      {(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V),
        lpReplicaCurrentGhost1} := by
    simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]
  unfold lpMatchingSeamSource lpMatchingGhostSource
  rw [hi, hj, hg]
  rw [Finset.symmDiff_eq_union hdij,
    Finset.symmDiff_eq_union hdghost]
  simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm]



theorem isEmpty_lpReplicaOffdiagDecoratedSource_of_commonSlotCard_le_two
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 2) :
    IsEmpty (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  constructor
  intro z
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  have hKcard : K.card <= 2 := by
    calc
      K.card <= Fintype.card
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1) :=
        Finset.card_le_univ K
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ <= 2 := hcard
  have hsources : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) z.1.1.1) K =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := d.2.2.2.2.1
  have hsourceCard := card_randomCurrent_sources_le_two_mul_card
    (StatMech.Sharpness.FluxEdgeCopy.endsM
      (lpReplicaCurrentGraph G sites) z.1.1.1) K
  rw [hsources, card_lpReplica_offdiagSource sites hsite hij] at hsourceCard
  omega



theorem lpReplicaOffdiagCrossToggleMaskHall_of_commonSlotCard_le_two
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 2) :
    LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
  classical
  unfold LPReplicaOffdiagCrossToggleMaskHall
  intro S
  have hS : S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z _
    exact (isEmpty_lpReplicaOffdiagDecoratedSource_of_commonSlotCard_le_two
      G sites hsite hij q hcard).false z
  simp [hS]



theorem lpReplicaOffdiagDecoratedSource_rank_three_all_falseCopies
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false = Finset.univ ∧
      ∀ c, d.1 c = (true, false) := by
  dsimp only
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1) = 3 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 3 := hcard
  have hKle : K.card <= 3 := by
    calc
      K.card <= Fintype.card
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1) :=
        Finset.card_le_univ K
      _ = 3 := hcopyCard
  have hsources : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) z.1.1.1) K =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := d.2.2.2.2.1
  have hsourceCard := card_randomCurrent_sources_le_two_mul_card
    (StatMech.Sharpness.FluxEdgeCopy.endsM
      (lpReplicaCurrentGraph G sites) z.1.1.1) K
  rw [hsources, card_lpReplica_offdiagSource sites hsite hij] at hsourceCard
  have hKcard : K.card = 3 := by omega
  have hKuniv : K = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ K)
    rw [Finset.card_univ, hcopyCard, hKcard]
  refine ⟨hKuniv, ?_⟩
  intro c
  have hc : c ∈ K := by rw [hKuniv]; simp
  simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
    Finset.mem_univ, true_and] using hc



theorem lpReplicaOffdiagDecoratedSource_eq_of_crossTrace_eq_of_isEmptySlots
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    [IsEmpty (LPReplicaOrbitCommonSlot G sites q)]
    (z w : LPReplicaOffdiagDecoratedSource G sites i j q)
    (htrace : lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z =
      lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q w) :
    z = w := by
  apply lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q
  rw [lpReplicaOrbitFourColorSlotState_eq_iff_crossNormalize_eq_and_rowMask_eq]
  refine ⟨htrace, ?_⟩
  ext x
  exact isEmptyElim x


theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiber_card_le_one_of_isEmptySlots
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    [IsEmpty (LPReplicaOrbitCommonSlot G sites q)]
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites i j q u).card <= 1 := by
  classical
  rw [Finset.card_le_one]
  intro z hz w hw
  apply lpReplicaOffdiagDecoratedSource_eq_of_crossTrace_eq_of_isEmptySlots
    G sites i j q
  exact (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2.symm



theorem lpReplicaOffdiagCrossTraceFiber_card_of_isEmptySlots_of_target_nonempty
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    [IsEmpty (LPReplicaOrbitCommonSlot G sites q)]
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (htarget : (lpReplicaOffdiagBalancedOutputCrossTraceFiber
      G sites i j q u).Nonempty) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
        G sites i j q u).card <=
      (lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u).card := by
  exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiber_card_le_one_of_isEmptySlots
    G sites i j q u).trans (Finset.Nonempty.card_pos htarget)



theorem lpReplicaOffdiagCrossToggleMaskNeighbors_eq_crossTraceFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    lpReplicaOffdiagCrossToggleMaskNeighbors G sites i j q z =
      lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) := by
  classical
  ext y
  simp [lpReplicaOffdiagCrossToggleMaskNeighbors,
    lpReplicaOffdiagBalancedOutputCrossTraceFiber,
    lpReplicaOffdiagCrossToggleMaskRelated_iff_crossTrace]



theorem lpReplicaOffdiagDecoratedSource_card_eq_sum_crossTraceFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (U : Finset (LPReplicaOrbitFourColorSlotState G sites q))
    (hU : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z ∈ U) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) =
      ∑ u ∈ U,
        (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
          G sites i j q u).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagDecoratedSourceCrossTraceFiber] using
    Finset.card_eq_sum_card_fiberwise (s :=
      (Finset.univ : Finset
        (LPReplicaOffdiagDecoratedSource G sites i j q)))
      (t := U) (f :=
        lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q) (by
          intro z _
          exact hU z)


theorem lpReplicaOffdiagBalancedOutputs_card_eq_sum_crossTraceFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (U : Finset (LPReplicaOrbitFourColorSlotState G sites q))
    (hU : forall y,
      y ∈ lpReplicaOffdiagBalancedOutputs G sites i j q ->
      lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y ∈ U) :
    (lpReplicaOffdiagBalancedOutputs G sites i j q).card =
      ∑ u ∈ U,
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q u).card := by
  classical
  simpa only [lpReplicaOffdiagBalancedOutputCrossTraceFiber] using
    Finset.card_eq_sum_card_fiberwise
      (s := lpReplicaOffdiagBalancedOutputs G sites i j q)
      (t := U) (f :=
        lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q) hU



theorem lpReplicaOffdiagCrossToggleMaskHall_of_crossTraceFiberCards
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : forall u : LPReplicaOrbitFourColorSlotState G sites q,
      (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
          G sites i j q u).card <=
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q u).card) :
    LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
  classical
  unfold LPReplicaOffdiagCrossToggleMaskHall
  intro S
  let trace := lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q
  let U := S.image trace
  have hpartition : S.card =
      ∑ u ∈ U, (S.filter fun z => trace z = u).card := by
    simpa only [U] using Finset.card_eq_sum_card_fiberwise
      (s := S) (t := U) (f := trace) (by
        intro z hz
        exact Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  have hdisj : ∀ u, u ∈ U -> ∀ v, v ∈ U -> u ≠ v ->
      Disjoint
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q u)
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q v) := by
    intro u _ v _ huv
    rw [Finset.disjoint_left]
    intro y hyu hyv
    have hu := (Finset.mem_filter.mp hyu).2
    have hv := (Finset.mem_filter.mp hyv).2
    exact huv (hu.symm.trans hv)
  calc
    S.card = ∑ u ∈ U, (S.filter fun z => trace z = u).card := hpartition
    _ <= ∑ u ∈ U,
        (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
          G sites i j q u).card := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.card_le_card
      intro z hz
      rw [Finset.mem_filter] at hz
      simp only [lpReplicaOffdiagDecoratedSourceCrossTraceFiber,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact hz.2
    _ <= ∑ u ∈ U,
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q u).card := by
      exact Finset.sum_le_sum fun u _ => hcard u
    _ = (U.biUnion
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q)).card :=
      (Finset.card_biUnion hdisj).symm
    _ <= (S.biUnion
        (lpReplicaOffdiagCrossToggleMaskNeighbors
          G sites i j q)).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨u, huU, hyu⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨z, hzS, hzu⟩ := Finset.mem_image.mp huU
      apply Finset.mem_biUnion.mpr
      refine ⟨z, hzS, ?_⟩
      rw [lpReplicaOffdiagCrossToggleMaskNeighbors_eq_crossTraceFiber]
      change lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z = u
        at hzu
      rw [hzu]
      exact hyu



theorem lpReplicaOffdiagCrossTraceFiberCards_of_maskHall
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hHall : LPReplicaOffdiagCrossToggleMaskHall G sites i j q)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
        G sites i j q u).card <=
      (lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u).card := by
  classical
  let sourceFiber := lpReplicaOffdiagDecoratedSourceCrossTraceFiber
    G sites i j q u
  let targetFiber := lpReplicaOffdiagBalancedOutputCrossTraceFiber
    G sites i j q u
  by_cases hsource : sourceFiber.Nonempty
  · have hunion : sourceFiber.biUnion
        (lpReplicaOffdiagCrossToggleMaskNeighbors G sites i j q) =
        targetFiber := by
      ext y
      constructor
      · intro hy
        obtain ⟨z, hz, hyz⟩ := Finset.mem_biUnion.mp hy
        rw [lpReplicaOffdiagCrossToggleMaskNeighbors_eq_crossTraceFiber]
          at hyz
        have hzu :
            lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z = u :=
          (Finset.mem_filter.mp hz).2
        simpa only [hzu, targetFiber] using hyz
      · intro hy
        obtain ⟨z, hz⟩ := hsource
        apply Finset.mem_biUnion.mpr
        refine ⟨z, hz, ?_⟩
        rw [lpReplicaOffdiagCrossToggleMaskNeighbors_eq_crossTraceFiber]
        have hzu :
            lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z = u :=
          (Finset.mem_filter.mp hz).2
        simpa only [hzu, targetFiber] using hy
    have h := hHall sourceFiber
    simpa only [sourceFiber, targetFiber, hunion] using h
  · have hempty : sourceFiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsource
    simp [sourceFiber, hempty]



theorem lpReplicaOffdiagCrossToggleMaskHall_iff_crossTraceFiberCards
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOffdiagCrossToggleMaskHall G sites i j q ↔
      forall u : LPReplicaOrbitFourColorSlotState G sites q,
        (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
            G sites i j q u).card <=
          (lpReplicaOffdiagBalancedOutputCrossTraceFiber
            G sites i j q u).card := by
  constructor
  · intro hHall u
    exact lpReplicaOffdiagCrossTraceFiberCards_of_maskHall
      G sites i j q hHall u
  · exact lpReplicaOffdiagCrossToggleMaskHall_of_crossTraceFiberCards
      G sites i j q


abbrev LPReplicaOffdiagCrossTraceFiberEmbedding
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :=
  {z // z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites i j q u} ↪
    {y // y ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiber
      G sites i j q u}



theorem lpReplicaOffdiagCrossToggleMaskHall_iff_traceFiberEmbeddings
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOffdiagCrossToggleMaskHall G sites i j q ↔
      forall u : LPReplicaOrbitFourColorSlotState G sites q,
        Nonempty (LPReplicaOffdiagCrossTraceFiberEmbedding
          G sites i j q u) := by
  rw [lpReplicaOffdiagCrossToggleMaskHall_iff_crossTraceFiberCards]
  apply forall_congr'
  intro u
  rw [Function.Embedding.nonempty_iff_card_le]
  simp only [Fintype.card_coe]


structure LPReplicaOffdiagCrossTraceFiberInjection
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  move : LPReplicaOffdiagDecoratedSource G sites i j q ->
    LPReplicaOffdiagDecoratedTarget G sites i j q
  output_mem : forall z,
    move z ∈ lpReplicaOffdiagBalancedOutputs G sites i j q
  trace_eq : forall z,
    lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q (move z) =
      lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z
  injective_on_trace : forall z w,
    lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z =
      lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q w ->
    move z = move w -> z = w



theorem lpReplicaOffdiagCrossToggleMaskHall_of_crossTraceFiberInjections
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hfiber : LPReplicaOffdiagCrossTraceFiberInjection G sites i j q) :
    LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
  classical
  have hmove : Function.Injective hfiber.move := by
    intro z w hzw
    have htrace :
        lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z =
          lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q w := by
      calc
        _ = lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q
            (hfiber.move z) := (hfiber.trace_eq z).symm
        _ = lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q
            (hfiber.move w) := congrArg
          (lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q) hzw
        _ = _ := hfiber.trace_eq w
    exact hfiber.injective_on_trace z w htrace hzw
  unfold LPReplicaOffdiagCrossToggleMaskHall
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective
    (lpReplicaOffdiagCrossToggleMaskNeighbors G sites i j q)).mpr
  refine ⟨hfiber.move, hmove, ?_⟩
  intro z
  simp only [lpReplicaOffdiagCrossToggleMaskNeighbors,
    Finset.mem_filter, Finset.mem_univ, true_and,
    lpReplicaOffdiagCrossToggleMaskRelated_iff_crossTrace]
  exact ⟨hfiber.output_mem z, hfiber.trace_eq z⟩



structure LPReplicaOffdiagCrossToggleSelector
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  selector : LPReplicaOffdiagDecoratedSource G sites i j q ->
    Finset (LPReplicaOrbitCommonSlot G sites q)
  output : LPReplicaOffdiagDecoratedSource G sites i j q ->
    LPReplicaOffdiagDecoratedTarget G sites i j q
  output_mem : forall z,
    output z ∈ lpReplicaOffdiagBalancedOutputs G sites i j q
  output_state : forall z,
    (lpReplicaOffdiagDecoratedTargetBranchedSlotState
      G sites i j q (output z)).2 =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q (selector z)
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
  collision_stable : forall z w,
    output z = output w -> selector z = selector w



structure LPReplicaOffdiagCrossToggleMatching
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  output : LPReplicaOffdiagDecoratedSource G sites i j q ->
    LPReplicaOffdiagDecoratedTarget G sites i j q
  output_mem : forall z,
    output z ∈ lpReplicaOffdiagBalancedOutputs G sites i j q
  output_injective : Function.Injective output
  realizes : forall z,
    ∃ P : Finset (LPReplicaOrbitCommonSlot G sites q),
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q (output z)).2 =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q P
          (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)



theorem LPReplicaOffdiagCrossToggleSelector.output_injective
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCrossToggleSelector G sites i j q) :
    Function.Injective s.output := by
  have hcross :=
    lpReplicaOrbitFourColorSlotBranchedCrossToggle_injective_of_collisionStable
      G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q)
      s.selector s.output
      (lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q) (by
        intro z w h
        exact s.collision_stable z w (congrArg Prod.fst h))
  intro z w houtput
  apply hcross
  apply Prod.ext
  · exact houtput
  · change lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (s.selector z)
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (s.selector w)
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w)
    rw [← s.output_state z, ← s.output_state w, houtput]



theorem nonempty_lpReplicaOffdiagCrossToggleSelector_iff_matching
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Nonempty (LPReplicaOffdiagCrossToggleSelector G sites i j q) ↔
      Nonempty (LPReplicaOffdiagCrossToggleMatching G sites i j q) := by
  constructor
  · rintro ⟨s⟩
    exact ⟨{
      output := s.output
      output_mem := s.output_mem
      output_injective := s.output_injective G sites i j q
      realizes := fun z => ⟨s.selector z, s.output_state z⟩
    }⟩
  · rintro ⟨m⟩
    let selector : LPReplicaOffdiagDecoratedSource G sites i j q ->
        Finset (LPReplicaOrbitCommonSlot G sites q) :=
      fun z => Classical.choose (m.realizes z)
    refine ⟨{
      selector := selector
      output := m.output
      output_mem := m.output_mem
      output_state := ?_
      collision_stable := ?_
    }⟩
    · intro z
      exact Classical.choose_spec (m.realizes z)
    · intro z w houtput
      have hzw := m.output_injective houtput
      subst w
      rfl



theorem nonempty_lpReplicaOffdiagCrossToggleMatching_iff_maskHall
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Nonempty (LPReplicaOffdiagCrossToggleMatching G sites i j q) ↔
      LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
  classical
  constructor
  · rintro ⟨m⟩
    unfold LPReplicaOffdiagCrossToggleMaskHall
    apply (Finset.all_card_le_biUnion_card_iff_exists_injective
      (lpReplicaOffdiagCrossToggleMaskNeighbors G sites i j q)).mpr
    refine ⟨m.output, m.output_injective, ?_⟩
    intro z
    simp only [lpReplicaOffdiagCrossToggleMaskNeighbors,
      Finset.mem_filter, Finset.mem_univ, true_and,
      LPReplicaOffdiagCrossToggleMaskRelated]
    exact ⟨m.output_mem z, m.realizes z⟩
  · intro hHall
    have hHall' : forall S : Finset
        (LPReplicaOffdiagDecoratedSource G sites i j q),
        S.card <= (S.biUnion
          (lpReplicaOffdiagCrossToggleMaskNeighbors G sites i j q)).card := by
      simpa only [LPReplicaOffdiagCrossToggleMaskHall] using hHall
    obtain ⟨move, hmove, hmem⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective
        (lpReplicaOffdiagCrossToggleMaskNeighbors G sites i j q)).mp
        hHall'
    refine ⟨{
      output := move
      output_mem := ?_
      output_injective := hmove
      realizes := ?_
    }⟩
    · intro z
      have hz := hmem z
      simp only [lpReplicaOffdiagCrossToggleMaskNeighbors,
        Finset.mem_filter, Finset.mem_univ, true_and,
        LPReplicaOffdiagCrossToggleMaskRelated] at hz
      exact hz.1
    · intro z
      have hz := hmem z
      simp only [lpReplicaOffdiagCrossToggleMaskNeighbors,
        Finset.mem_filter, Finset.mem_univ, true_and,
        LPReplicaOffdiagCrossToggleMaskRelated] at hz
      exact hz.2


theorem nonempty_lpReplicaOffdiagCrossToggleSelector_iff_maskHall
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Nonempty (LPReplicaOffdiagCrossToggleSelector G sites i j q) ↔
      LPReplicaOffdiagCrossToggleMaskHall G sites i j q :=
  (nonempty_lpReplicaOffdiagCrossToggleSelector_iff_matching
    G sites i j q).trans
      (nonempty_lpReplicaOffdiagCrossToggleMatching_iff_maskHall
        G sites i j q)



theorem lpReplicaOffdiagBalancedOutputCard_of_crossToggleSelector
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCrossToggleSelector G sites i j q) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagBalancedOutputs G sites i j q).card := by
  let move : LPReplicaOffdiagDecoratedSource G sites i j q ->
      {y // y ∈ lpReplicaOffdiagBalancedOutputs G sites i j q} :=
    fun z => ⟨s.output z, s.output_mem z⟩
  have hmove : Function.Injective move := by
    intro z w h
    apply s.output_injective G sites i j q
    exact congrArg Subtype.val h
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective move hmove


theorem lpReplicaOffdiagBalancedHall_of_crossToggleSelector
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCrossToggleSelector G sites i j q) :
    LPReplicaOffdiagBalancedHall G sites i j q :=
  lpReplicaOffdiagBalancedHall_of_outputCard G sites i j q
    (lpReplicaOffdiagBalancedOutputCard_of_crossToggleSelector
      G sites i j q s)



theorem lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleSelector
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCrossToggleSelector G sites i j q) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q :=
  lpReplicaOffdiagOrbitAtomCardInequality_of_balancedOutputCard
    G sites i j q
      (lpReplicaOffdiagBalancedOutputCard_of_crossToggleSelector
        G sites i j q s)


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleMaskHall
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hHall : LPReplicaOffdiagCrossToggleMaskHall G sites i j q) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  obtain ⟨s⟩ :=
    (nonempty_lpReplicaOffdiagCrossToggleSelector_iff_maskHall
      G sites i j q).mpr hHall
  exact lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleSelector
    G sites i j q s



theorem lpReplicaOffdiagOrbitAtomCardInequality_zero
    (G : SimpleGraph V) (sites : I -> V) (i j : I) :
    LPReplicaOffdiagOrbitAtomCardInequality
      G sites i j (fun _ => 0) :=
  lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleMaskHall
    G sites i j (fun _ => 0)
      (lpReplicaOffdiagCrossToggleMaskHall_zero G sites i j)



theorem lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_two
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 2) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q :=
  lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleMaskHall
    G sites i j q
      (lpReplicaOffdiagCrossToggleMaskHall_of_commonSlotCard_le_two
        G sites hsite hij q hcard)

end

end StatMech.Ising
