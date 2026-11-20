/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching
import Code.Ising.LebowitzPfisterReplicaOrbitPairedCutHallExact
import Code.Ising.LebowitzPfisterReplicaOrbitExactTagProjection
import Code.Walls.gc7componenteven











open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaPairedCutInjectionDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



theorem lpReplicaOrientedFourColorSlotState_ofRowGate
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    lpReplicaOrientedFourColorSlotState G sites A
        (B.map lpReplicaCurrentReflect.toEmbedding) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A
          (B.map lpReplicaCurrentReflect.toEmbedding) q
          (lpReplicaDecoratedOrbitAtomOfRowGate
            G sites m q tag A B hm hgate L)) =
      lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag := by
  unfold lpReplicaOrientedFourColorSlotState
  rw [lpReplicaOrientedFourColorTag_ofRowGate]
  rfl



theorem lpReplicaOrbitFourColorSlotStateOfTag_cast_profile
    (G : SimpleGraph V) (sites : I -> V)
    (q m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (h : n = m)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hn : lpReplicaSymmetrizedProfile G sites n = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaOrbitFourColorSlotStateOfTag G sites q n hn
        (cast (congrArg (LPReplicaProfileOrbitLabel G sites q) h.symm) L)
        (fun c => tag (cast (congrArg
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites)) h) c)) =
      lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag := by
  subst n
  rfl





def LPReplicaPartialReflectCommonSlotCompatible
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)) : Prop :=
  forall c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m,
    lpReplicaProfileCopyEquivCommonSlot G sites q
        (lpReplicaPartialReflectProfile G sites m
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m P))
        ((lpReplicaSymmetrizedProfile_partialReflectCopies
          G sites m P).trans hm)
        (lpReplicaProfileOrbitLabelPartialReflectCopies
          G sites q m hm P L)
        (lpReplicaPartialReflectCopyEquiv G sites m P c) =
      lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c



noncomputable def lpReplicaPartialReflectTransportTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites)
      (lpReplicaPartialReflectProfile G sites m
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m P)) -> LPReplicaRowTag :=
  fun d => lpReplicaToggleRows G sites m P tag
    ((lpReplicaPartialReflectCopyEquiv G sites m P).symm d)

set_option maxHeartbeats 800000 in



theorem lpReplicaPartialReflectTransportTag_cast_eq_coupledRaw
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (d : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m P))) :
    lpReplicaPartialReflectTransportTag G sites m P tag
        (cast (congrArg (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites))
            (lpReplicaCollisionProfile_compl_eq_partialReflectProfile
              G sites m P)) d) =
      lpReplicaCoupledReflectToggleTagRaw G sites m P tag d := by
  unfold lpReplicaPartialReflectTransportTag
    lpReplicaCoupledReflectToggleTagRaw lpReplicaPartialReflectTagRaw
    lpReplicaPartialReflectCopyEquiv
  apply congrArg (lpReplicaToggleRows G sites m P tag)
  apply congrArg (lpReplicaPartialReflectCopyEquivRaw G sites m P).symm
  exact (Equiv.cast (congrArg (StatMech.Sharpness.FluxEdgeCopy.Copy
    (lpReplicaCurrentGraph G sites))
      (lpReplicaCollisionProfile_compl_eq_partialReflectProfile
        G sites m P))).symm_apply_apply d



theorem lpReplicaOrbitFourColorSlotState_partialReflect_of_compatible
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hcompat : LPReplicaPartialReflectCommonSlotCompatible
      G sites q m hm L P) :
    lpReplicaOrbitFourColorSlotStateOfTag G sites q
        (lpReplicaPartialReflectProfile G sites m
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m P))
        ((lpReplicaSymmetrizedProfile_partialReflectCopies
          G sites m P).trans hm)
        (lpReplicaProfileOrbitLabelPartialReflectCopies
          G sites q m hm P L)
        (lpReplicaPartialReflectTransportTag G sites m P tag) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
        (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) := by
  apply LPReplicaOrbitFourColorSlotState.ext
  · rw [lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_allocation]
    rfl
  · rw [lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_color]
    funext x
    let Es := lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
    let Et := lpReplicaProfileCopyEquivCommonSlot G sites q
      (lpReplicaPartialReflectProfile G sites m
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m P))
      ((lpReplicaSymmetrizedProfile_partialReflectCopies
        G sites m P).trans hm)
      (lpReplicaProfileOrbitLabelPartialReflectCopies
        G sites q m hm P L)
    let E := lpReplicaPartialReflectCopyEquiv G sites m P
    let c := Es.symm x.1
    have hEt : Et (E c) = x.1 := by
      rw [hcompat c]
      exact Es.apply_symm_apply x.1
    have hinv : Et.symm x.1 = E c := by
      apply Et.injective
      rw [Et.apply_symm_apply, hEt]
    change lpReplicaRowTagEquivFin4
        (lpReplicaPartialReflectTransportTag G sites m P tag
          (Et.symm x.1)) =
      lpReplicaRowTagEquivFin4
        (lpReplicaToggleRows G sites m P tag (Es.symm x.1))
    rw [hinv]
    simp only [lpReplicaPartialReflectTransportTag, E, c, Es,
      Equiv.symm_apply_apply]



theorem lpReplicaOrientedFourColorSlotState_cast_targetBoundary
    (G : SimpleGraph V) (sites : I -> V)
    (A D E : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (h : D = E) (x : LPReplicaDecoratedOrbitAtom G sites A D q) :
    lpReplicaOrientedFourColorSlotState G sites A E q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A E q
          (cast (congrArg
            (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) h) x)) =
      lpReplicaOrientedFourColorSlotState G sites A D q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor
          G sites A D q x) := by
  subst E
  rfl



theorem lpReplicaOrientedFourColorSlotState_cast_sourceBoundary
    (G : SimpleGraph V) (sites : I -> V)
    (A C D : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (h : A = C) (x : LPReplicaDecoratedOrbitAtom G sites A D q) :
    lpReplicaOrientedFourColorSlotState G sites C D q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites C D q
          (cast (congrArg
            (fun Z => LPReplicaDecoratedOrbitAtom G sites Z D q) h) x)) =
      lpReplicaOrientedFourColorSlotState G sites A D q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor
          G sites A D q x) := by
  subst C
  rfl

set_option maxHeartbeats 800000 in



theorem lpReplicaDecoratedOrbitAtomOfCoupledPairedCut_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaCoupledPairedCut G sites m B tag) :
    let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
    lpReplicaOrientedFourColorSlotState G sites (B ∆ D) D q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites
          (B ∆ D) D q
          (lpReplicaDecoratedOrbitAtomOfCoupledPairedCut
            G sites m q B tag horbit hgate L cut)) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies
          G sites q m horbit L cut.selector)
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m horbit L tag) := by
  dsimp only
  unfold lpReplicaDecoratedOrbitAtomOfCoupledPairedCut
  dsimp only [id]
  rw [lpReplicaOrientedFourColorSlotState_cast_targetBoundary]
  rw [lpReplicaOrientedFourColorSlotState_ofRowGate]
  · exact lpReplicaOrbitFourColorSlotState_canonicalPartialReflect
      G sites q m horbit L cut.selector tag
  · exact lpReplica_half_symmDiff_reflect_fixed cut.half

set_option maxHeartbeats 800000 in



theorem lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (hgate : LPReplicaRowGate G sites m ∅ B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
    lpReplicaOrientedFourColorSlotState G sites D (B ∆ D) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites
          D (B ∆ D) q
          (lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut
            G sites m q B tag horbit hB hgate L cut)) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies
          G sites q m horbit L cut.selector)
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m horbit L tag) := by
  dsimp only
  unfold lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut
  dsimp only [id]
  rw [lpReplicaOrientedFourColorSlotState_cast_targetBoundary]
  rw [lpReplicaOrientedFourColorSlotState_ofRowGate]
  · exact lpReplicaOrbitFourColorSlotState_canonicalPartialReflect
      G sites q m horbit L cut.selector tag
  · rw [lpReplica_map_symmDiff, hB,
      lpReplica_half_symmDiff_reflect_fixed]



theorem lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B A Dtarget : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaCoupledPairedCut G sites m B tag)
    (hA : B ∆ (cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding) = A)
    (hD : cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding = Dtarget) :
    lpReplicaOrientedFourColorSlotState G sites A Dtarget q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites
          A Dtarget q
          (lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast
            G sites m q B A Dtarget tag horbit hgate L cut hA hD)) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies
          G sites q m horbit L cut.selector)
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m horbit L tag) := by
  unfold lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast
  dsimp only [id]
  rw [lpReplicaOrientedFourColorSlotState_cast_targetBoundary]
  rw [lpReplicaOrientedFourColorSlotState_cast_sourceBoundary]
  exact lpReplicaDecoratedOrbitAtomOfCoupledPairedCut_slotState
    G sites m q B tag horbit hgate L cut
  all_goals assumption



theorem lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B A Dtarget : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (hgate : LPReplicaRowGate G sites m ∅ B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag)
    (hA : cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding = A)
    (hD : B ∆ (cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding) = Dtarget) :
    lpReplicaOrientedFourColorSlotState G sites A Dtarget q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites
          A Dtarget q
          (lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast
            G sites m q B A Dtarget tag horbit hB hgate L cut hA hD)) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies
          G sites q m horbit L cut.selector)
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m horbit L tag) := by
  unfold lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast
  dsimp only [id]
  rw [lpReplicaOrientedFourColorSlotState_cast_targetBoundary]
  rw [lpReplicaOrientedFourColorSlotState_cast_sourceBoundary]
  exact lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut_slotState
    G sites m q B tag horbit hB hgate L cut
  all_goals assumption



theorem lpReplica_even_card_half_symmDiff_reflect_inter_leftSide
    (X : Finset (LPReplicaCurrentVertex V)) (hX : Even X.card) :
    Even ((X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∩
      lpReplicaCurrentLeftSide).card := by
  classical
  let L := lpReplicaCurrentLeftSide (V := V)
  let XL := X ∩ L
  let XR := X \ L
  let YR := XR.map lpReplicaCurrentReflect.toEmbedding
  have hsymm (x : LPReplicaCurrentVertex V) :
      lpReplicaCurrentReflect.symm x = lpReplicaCurrentReflect x := by
    apply lpReplicaCurrentReflect.injective
    rw [Equiv.apply_symm_apply, lpReplicaCurrentReflect_involutive]
  have hdecomp : (X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∩ L =
      XL ∆ YR := by
    ext x
    rcases x with (x | b)
    · rcases x with x | x <;>
        simp [L, XL, XR, YR, Finset.mem_symmDiff,
          lpReplicaCurrentLeftSide, lpReplicaCurrentLeftEmbedding,
          lpReplicaCurrentGhost0, hsymm]
    · cases b <;>
        simp [L, XL, XR, YR, Finset.mem_symmDiff,
          lpReplicaCurrentLeftSide, lpReplicaCurrentLeftEmbedding,
          lpReplicaCurrentGhost0, hsymm]
  have hYR : YR.card = XR.card := by
    dsimp only [YR]
    rw [Finset.card_map]
  have hsum : Even (XL.card + YR.card) := by
    rw [hYR]
    have hpartition := Finset.card_sdiff_add_card_inter X L
    dsimp only [XL, XR]
    rw [add_comm]
    rwa [hpartition]
  have hdisj : Disjoint (XL \ YR) (YR \ XL) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hx).1
  have hcard : (XL ∆ YR).card =
      (XL \ YR).card + (YR \ XL).card := by
    rw [show XL ∆ YR = (XL \ YR) ∪ (YR \ XL) by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]]
    exact Finset.card_union_of_disjoint hdisj
  rcases hsum with ⟨k, hk⟩
  have hXL := Finset.card_sdiff_add_card_inter XL YR
  have hYR' := Finset.card_sdiff_add_card_inter YR XL
  rw [Finset.inter_comm YR XL] at hYR'
  rw [hdecomp, hcard]
  refine ⟨k - (XL ∩ YR).card, ?_⟩
  omega


def LPReplicaEvenLeftBoundary (X : Finset (LPReplicaCurrentVertex V)) : Prop :=
  Even (X ∩ lpReplicaCurrentLeftSide).card


theorem LPReplicaEvenLeftBoundary.symmDiff
    {X Y : Finset (LPReplicaCurrentVertex V)}
    (hX : LPReplicaEvenLeftBoundary X)
    (hY : LPReplicaEvenLeftBoundary Y) :
    LPReplicaEvenLeftBoundary (X ∆ Y) := by
  let A := X ∩ lpReplicaCurrentLeftSide
  let B := Y ∩ lpReplicaCurrentLeftSide
  have hinter : (X ∆ Y) ∩ lpReplicaCurrentLeftSide = A ∆ B := by
    ext x
    simp only [A, B, Finset.mem_inter, Finset.mem_symmDiff]
    tauto
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hx).1
  have hcard : (A ∆ B).card = (A \ B).card + (B \ A).card := by
    rw [show A ∆ B = (A \ B) ∪ (B \ A) by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]]
    exact Finset.card_union_of_disjoint hdisj
  change Even A.card at hX
  change Even B.card at hY
  rcases hX with ⟨a, ha⟩
  rcases hY with ⟨b, hb⟩
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hB
  rw [LPReplicaEvenLeftBoundary, hinter, hcard]
  refine ⟨a + b - (A ∩ B).card, ?_⟩
  omega



theorem lpReplica_doubledBoundary_evenLeft
    (X : Finset (LPReplicaCurrentVertex V)) (hX : Even X.card) :
    LPReplicaEvenLeftBoundary
      (X ∆ X.map lpReplicaCurrentReflect.toEmbedding) :=
  lpReplica_even_card_half_symmDiff_reflect_inter_leftSide X hX



theorem lpReplica_evenLeft_after_doubledBoundary
    (A X : Finset (LPReplicaCurrentVertex V))
    (hA : LPReplicaEvenLeftBoundary A) (hX : Even X.card) :
    LPReplicaEvenLeftBoundary
      (A ∆ (X ∆ X.map lpReplicaCurrentReflect.toEmbedding)) :=
  hA.symmDiff (lpReplica_doubledBoundary_evenLeft X hX)



theorem lpReplica_doubledThenSeam_targetBoundaries
    (Si Sj T Sk D : Finset (LPReplicaCurrentVertex V))
    (hD : D = Si ∆ Sk) :
    D ∆ Sk = Si ∧
      ((Si ∆ Sj ∆ T) ∆ D) ∆ Sk = Sj ∆ T := by
  subst D
  constructor <;>
    ext x <;>
    simp only [Finset.mem_symmDiff] <;>
    tauto




theorem lpReplicaBalancedComponentBoundary_ne_seam_symmDiff_ghost
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (i : I) :
    lpReplicaBalancedComponentBoundary G sites m B ∅ tag ≠
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 := by
  intro hboundary
  have htarget : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource lpReplicaCurrentGhost0
          lpReplicaCurrentGhost1 := by
    simp [lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff]
  have hsource : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈
      lpReplicaBalancedComponentBoundary G sites m B ∅ tag := by
    rwa [hboundary]
  change (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈
    (B ∩ StatMech.Sharpness.RandomCurrent.compOf
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m)
      (lpReplicaRowCopies G sites m tag false)
      lpReplicaCurrentGhost1) ∆ ∅ at hsource
  simp [Finset.mem_symmDiff,
    StatMech.Sharpness.RandomCurrent.mem_compOf] at hsource
  exact hgate.2.2.1
    (StatMech.Sharpness.RandomCurrent.connK_symm _ _ hsource.2)




theorem lpReplicaRowGate_rightPairedCut_thenSeam
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Si Sj T Sk : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m ∅ (Si ∆ Sj ∆ T) tag)
    (cut : LPReplicaRightCoupledPairedCut
      G sites m (Si ∆ Sj ∆ T) tag)
    (hD : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding =
      Si ∆ Sk)
    (Q : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ cut.selector))
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m cut.selector))))
    (hfalse : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m
            (Finset.univ \ cut.selector))
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m cut.selector)))
      (Q.filter fun c =>
        ((lpReplicaCoupledReflectToggleTagRaw
          G sites m cut.selector tag) c).2 = false) = Sk)
    (htrue : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m
            (Finset.univ \ cut.selector))
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m cut.selector)))
      (Q.filter fun c =>
        ((lpReplicaCoupledReflectToggleTagRaw
          G sites m cut.selector tag) c).2 = true) = ∅)
    (hdisc0 : ¬ StatMech.Sharpness.RandomCurrent.connK
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m
            (Finset.univ \ cut.selector))
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m cut.selector)))
      (lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m
            (Finset.univ \ cut.selector))
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m cut.selector))
        (lpReplicaToggleRows G sites _ Q
          (lpReplicaCoupledReflectToggleTagRaw
            G sites m cut.selector tag)) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
    (hdisc1 : ¬ StatMech.Sharpness.RandomCurrent.connK
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m
            (Finset.univ \ cut.selector))
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m cut.selector)))
      (lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m
            (Finset.univ \ cut.selector))
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m cut.selector))
        (lpReplicaToggleRows G sites _ Q
          (lpReplicaCoupledReflectToggleTagRaw
            G sites m cut.selector tag)) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m
          (Finset.univ \ cut.selector))
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m cut.selector))
      Si (Sj ∆ T)
      (lpReplicaToggleRows G sites _ Q
        (lpReplicaCoupledReflectToggleTagRaw
          G sites m cut.selector tag)) := by
  let target := lpReplicaCollisionProfile G sites
    (StatMech.Sharpness.FluxEdgeCopy.profileFlux
      (lpReplicaCurrentGraph G sites) m (Finset.univ \ cut.selector))
    (StatMech.Sharpness.FluxEdgeCopy.profileFlux
      (lpReplicaCurrentGraph G sites) m cut.selector)
  let moved := lpReplicaCoupledReflectToggleTagRaw
    G sites m cut.selector tag
  let D := cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding
  have hpaired : LPReplicaRowGate G sites target D
      ((Si ∆ Sj ∆ T) ∆ D) moved := by
    simpa only [target, moved, D] using
      lpReplicaRowGate_rightCoupledPairedCut
        G sites m (Si ∆ Sj ∆ T) tag hgate cut
  have htoggled := lpReplicaRowGate_toggle G sites target D
    ((Si ∆ Sj ∆ T) ∆ D) moved Q hpaired htrue hdisc0 hdisc1
  dsimp only at htoggled
  rw [hfalse] at htoggled
  have hb := lpReplica_doubledThenSeam_targetBoundaries Si Sj T Sk D (by
    simpa only [D] using hD)
  rw [hb.1, hb.2] at htoggled
  exact htoggled



theorem LPReplicaRightCoupledPairedCut.half_card_even
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    Even cut.half.card := by
  have h := StatMech.Walls.gc7_total_handshake_edgeCopy
    (G := lpReplicaCurrentGraph G sites) m
    (lpReplicaCurrentCopies G sites m tag false false ∩ cut.selector)
  rw [cut.falseSource0] at h
  exact h



theorem LPReplicaRightCoupledPairedCut.doubledHalf_ne_seamSource
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag)
    (i : I) :
    cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding ≠
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i := by
  intro hD
  have heven := lpReplica_even_card_half_symmDiff_reflect_inter_leftSide
    cut.half (cut.half_card_even G sites m B tag)
  have hseam :
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∩
        lpReplicaCurrentLeftSide) =
      {lpReplicaCurrentLeft sites i} := by
    ext x
    rcases x with (x | b)
    · rcases x with x | x <;>
        simp [lpMatchingSeamSource, lpReplicaCurrentLeft,
          lpReplicaCurrentRight, lpReplicaCurrentLeftSide,
          lpReplicaCurrentLeftEmbedding, lpReplicaCurrentGhost0,
          Finset.mem_symmDiff]
    · cases b <;>
        simp [lpMatchingSeamSource, lpReplicaCurrentLeft,
          lpReplicaCurrentRight, lpReplicaCurrentLeftSide,
          lpReplicaCurrentLeftEmbedding, lpReplicaCurrentGhost0,
          Finset.mem_symmDiff]
  rw [hD, hseam] at heven
  norm_num at heven

set_option maxHeartbeats 4000000 in



theorem lpReplicaOffdiagDecoratedSourceSlotState_fixedRowGateData
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let B := lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
    let hfixed : B.map lpReplicaCurrentReflect.toEmbedding = B := by
      simpa only [B] using
        lpReplicaCurrentReflect_offdiagSource G sites i j
    let d := lpReplicaDecoratedOrbitAtomFixedRowGateData
      G sites ∅ B q hfixed z
    lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z =
      lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1
        z.1.1.2 z.2.2 d.1 := by
  dsimp only
  unfold lpReplicaOffdiagDecoratedSourceSlotState
    lpReplicaOrientedFourColorSlotState
    lpReplicaOrbitFourColorSlotStateOfTag
    lpReplicaDecoratedOrbitAtomFixedRowGateData
    lpReplicaOrientedFourColorTag
  rfl





structure LPReplicaOffdiagCoupledPairedCrossToggleInjection
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  selector : LPReplicaOffdiagDecoratedSource G sites i j q ->
    Finset (LPReplicaOrbitCommonSlot G sites q)
  output : LPReplicaOffdiagDecoratedSource G sites i j q ->
    LPReplicaOffdiagDecoratedTarget G sites i j q
  output_valid : forall z,
    LPReplicaOffdiagCoupledPairedOutput G sites i j q (output z)
  output_state : forall z,
    (lpReplicaOffdiagDecoratedTargetBranchedSlotState
      G sites i j q (output z)).2 =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q (selector z)
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
  collision_stable : forall z w,
    output z = output w -> selector z = selector w


noncomputable def lpReplicaOrbitCanonicalFirstSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
    LPReplicaOrbitCommonSlot G sites q :=
  (Fintype.equivFin (LPReplicaOrbitCommonSlot G sites q)).symm
    ⟨0, lt_of_lt_of_le (by omega) hcard⟩


noncomputable def lpReplicaOrbitCanonicalSecondSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
    LPReplicaOrbitCommonSlot G sites q :=
  (Fintype.equivFin (LPReplicaOrbitCommonSlot G sites q)).symm
    ⟨1, hcard⟩


theorem lpReplicaOrbitCanonicalFirstSlot_ne_secondSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
    lpReplicaOrbitCanonicalFirstSlot G sites q hcard ≠
      lpReplicaOrbitCanonicalSecondSlot G sites q hcard := by
  intro h
  have hfin := (Fintype.equivFin
    (LPReplicaOrbitCommonSlot G sites q)).symm.injective h
  have hval := congrArg Fin.val hfin
  norm_num at hval


noncomputable def lpReplicaOrbitCanonicalFirstTwoSlots
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
    Finset (LPReplicaOrbitCommonSlot G sites q) :=
  {lpReplicaOrbitCanonicalFirstSlot G sites q hcard,
    lpReplicaOrbitCanonicalSecondSlot G sites q hcard}

@[simp] theorem lpReplicaOrbitCanonicalFirstTwoSlots_card
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
    (lpReplicaOrbitCanonicalFirstTwoSlots G sites q hcard).card = 2 := by
  simp [lpReplicaOrbitCanonicalFirstTwoSlots,
    lpReplicaOrbitCanonicalFirstSlot_ne_secondSlot G sites q hcard]



noncomputable def lpReplicaOrbitCommonSlotOrderKey
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOrbitCommonSlot G sites q -> Lex (Nat × Lex (Nat × Nat))
  | Sum.inl ⟨e, k⟩ =>
      toLex (0, toLex (lpReplicaCurrentEdgeRank G sites e.1, k))
  | Sum.inr ⟨e, k⟩ =>
      toLex (1, toLex (lpReplicaCurrentEdgeRank G sites e.1, k))

theorem lpReplicaOrbitCommonSlotOrderKey_injective
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Injective (lpReplicaOrbitCommonSlotOrderKey G sites q) := by
  intro x y h
  rcases x with ⟨e, k⟩ | ⟨e, k⟩ <;>
    rcases y with ⟨f, l⟩ | ⟨f, l⟩
  · change (0, toLex ((lpReplicaCurrentEdgeRank G sites e.1 : Nat),
        (k : Nat))) =
      (0, toLex ((lpReplicaCurrentEdgeRank G sites f.1 : Nat),
        (l : Nat))) at h
    have h' := congrArg (fun z : Nat × Lex (Nat × Nat) => z.2) h
    change ((lpReplicaCurrentEdgeRank G sites e.1 : Nat), (k : Nat)) =
      ((lpReplicaCurrentEdgeRank G sites f.1 : Nat), (l : Nat)) at h'
    have hrank : lpReplicaCurrentEdgeRank G sites e.1 =
        lpReplicaCurrentEdgeRank G sites f.1 := Fin.ext
          (congrArg (fun z : Nat × Nat => z.1) h')
    have hef : e.1 = f.1 :=
      lpReplicaCurrentEdgeRank_injective G sites hrank
    have he : e = f := Subtype.ext hef
    subst f
    have hkl : k = l := Fin.ext
      (congrArg (fun z : Nat × Nat => z.2) h')
    subst l
    rfl
  · change (0, toLex ((lpReplicaCurrentEdgeRank G sites e.1 : Nat),
        (k : Nat))) =
      (1, toLex ((lpReplicaCurrentEdgeRank G sites f.1 : Nat),
        (l : Nat))) at h
    exact (Nat.zero_ne_one (congrArg
      (fun z : Nat × Lex (Nat × Nat) => z.1) h)).elim
  · change (1, toLex ((lpReplicaCurrentEdgeRank G sites e.1 : Nat),
        (k : Nat))) =
      (0, toLex ((lpReplicaCurrentEdgeRank G sites f.1 : Nat),
        (l : Nat))) at h
    exact (Nat.one_ne_zero (congrArg
      (fun z : Nat × Lex (Nat × Nat) => z.1) h)).elim
  · change (1, toLex ((lpReplicaCurrentEdgeRank G sites e.1 : Nat),
        (k : Nat))) =
      (1, toLex ((lpReplicaCurrentEdgeRank G sites f.1 : Nat),
        (l : Nat))) at h
    have h' := congrArg (fun z : Nat × Lex (Nat × Nat) => z.2) h
    change ((lpReplicaCurrentEdgeRank G sites e.1 : Nat), (k : Nat)) =
      ((lpReplicaCurrentEdgeRank G sites f.1 : Nat), (l : Nat)) at h'
    have hrank : lpReplicaCurrentEdgeRank G sites e.1 =
        lpReplicaCurrentEdgeRank G sites f.1 := Fin.ext
          (congrArg (fun z : Nat × Nat => z.1) h')
    have hef : e.1 = f.1 :=
      lpReplicaCurrentEdgeRank_injective G sites hrank
    have he : e = f := Subtype.ext hef
    subst f
    have hkl : k = l := Fin.ext
      (congrArg (fun z : Nat × Nat => z.2) h')
    subst l
    rfl


noncomputable def lpReplicaOrbitCanonicalLastSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
    LPReplicaOrbitCommonSlot G sites q := by
  letI : LinearOrder (LPReplicaOrbitCommonSlot G sites q) :=
    LinearOrder.lift' (lpReplicaOrbitCommonSlotOrderKey G sites q)
      (lpReplicaOrbitCommonSlotOrderKey_injective G sites q)
  let E := ((Finset.univ : Finset
    (LPReplicaOrbitCommonSlot G sites q)).orderIsoOfFin rfl)
  exact (E ⟨Fintype.card (LPReplicaOrbitCommonSlot G sites q) - 1, by
    simpa only [Finset.card_univ] using
      (Nat.sub_lt (by omega) (by omega))⟩).1


noncomputable def lpReplicaOrbitCanonicalPenultimateSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
    LPReplicaOrbitCommonSlot G sites q := by
  letI : LinearOrder (LPReplicaOrbitCommonSlot G sites q) :=
    LinearOrder.lift' (lpReplicaOrbitCommonSlotOrderKey G sites q)
      (lpReplicaOrbitCommonSlotOrderKey_injective G sites q)
  let E := ((Finset.univ : Finset
    (LPReplicaOrbitCommonSlot G sites q)).orderIsoOfFin rfl)
  exact (E ⟨Fintype.card (LPReplicaOrbitCommonSlot G sites q) - 2, by
    simpa only [Finset.card_univ] using
      (Nat.sub_lt (by omega) (by omega))⟩).1

set_option maxHeartbeats 800000 in

theorem lpReplicaOrbitCanonicalPenultimateSlot_ne_lastSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
    lpReplicaOrbitCanonicalPenultimateSlot G sites q hcard ≠
      lpReplicaOrbitCanonicalLastSlot G sites q hcard := by
  intro h
  letI : LinearOrder (LPReplicaOrbitCommonSlot G sites q) :=
    LinearOrder.lift' (lpReplicaOrbitCommonSlotOrderKey G sites q)
      (lpReplicaOrbitCommonSlotOrderKey_injective G sites q)
  let E := (Finset.univ : Finset
    (LPReplicaOrbitCommonSlot G sites q)).orderIsoOfFin Finset.card_univ
  let a : Fin (Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :=
    ⟨Fintype.card (LPReplicaOrbitCommonSlot G sites q) - 2, by omega⟩
  let b : Fin (Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :=
    ⟨Fintype.card (LPReplicaOrbitCommonSlot G sites q) - 1, by omega⟩
  have hsub : E a = E b := by
    apply Subtype.ext
    change (E a).1 = (E b).1
    simpa only [a, b, lpReplicaOrbitCanonicalPenultimateSlot,
      lpReplicaOrbitCanonicalLastSlot] using h
  have hfin : a = b := E.injective hsub
  have hval := congrArg (fun z => z.val) hfin
  dsimp only [a, b] at hval
  omega


noncomputable def lpReplicaOrbitCanonicalLastTwoSlots
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
    Finset (LPReplicaOrbitCommonSlot G sites q) :=
  {lpReplicaOrbitCanonicalPenultimateSlot G sites q hcard,
    lpReplicaOrbitCanonicalLastSlot G sites q hcard}

@[simp] theorem lpReplicaOrbitCanonicalLastTwoSlots_card
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
    (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard).card = 2 := by
  simp [lpReplicaOrbitCanonicalLastTwoSlots,
    lpReplicaOrbitCanonicalPenultimateSlot_ne_lastSlot G sites q hcard]



def LPReplicaOrbitCommonSlotTerminal
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q)) : Prop :=
  forall x, x ∈ P -> forall y,
    lpReplicaOrbitCommonSlotOrderKey G sites q x <=
      lpReplicaOrbitCommonSlotOrderKey G sites q y -> y ∈ P

set_option maxHeartbeats 800000 in


theorem lpReplicaOrbitCanonicalLastTwoSlots_terminal
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
    LPReplicaOrbitCommonSlotTerminal G sites q
      (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard) := by
  intro x hx y hxy
  letI : LinearOrder (LPReplicaOrbitCommonSlot G sites q) :=
    LinearOrder.lift' (lpReplicaOrbitCommonSlotOrderKey G sites q)
      (lpReplicaOrbitCommonSlotOrderKey_injective G sites q)
  let E := (Finset.univ : Finset
    (LPReplicaOrbitCommonSlot G sites q)).orderIsoOfFin Finset.card_univ
  have hxy' : x <= y := hxy
  let n := Fintype.card (LPReplicaOrbitCommonSlot G sites q)
  let a : Fin n := ⟨n - 2, by dsimp only [n]; omega⟩
  let b : Fin n := ⟨n - 1, by dsimp only [n]; omega⟩
  have hEa : (E a).1 =
      lpReplicaOrbitCanonicalPenultimateSlot G sites q hcard := by
    simp only [a, n, E, lpReplicaOrbitCanonicalPenultimateSlot]
    rfl
  have hEb : (E b).1 =
      lpReplicaOrbitCanonicalLastSlot G sites q hcard := by
    simp only [b, n, E, lpReplicaOrbitCanonicalLastSlot]
    rfl
  have hmem : x = lpReplicaOrbitCanonicalPenultimateSlot G sites q hcard ∨
      x = lpReplicaOrbitCanonicalLastSlot G sites q hcard := by
    simpa only [lpReplicaOrbitCanonicalLastTwoSlots, Finset.mem_insert,
      Finset.mem_singleton] using hx
  let iy := E.symm ⟨y, Finset.mem_univ y⟩
  have hEiy : (E iy).1 = y := by
    exact congrArg Subtype.val
      (E.apply_symm_apply ⟨y, Finset.mem_univ y⟩)
  have hiy : iy.val = n - 2 ∨ iy.val = n - 1 := by
    rcases hmem with hxpen | hxlast
    · have hindex : a <= iy := by
        apply E.le_iff_le.mp
        change (E a).1 <= (E iy).1
        rw [hEa, hEiy]
        simpa only [hxpen] using hxy'
      have hindexVal : a.val <= iy.val := hindex
      have hilt := iy.isLt
      dsimp only [a] at hindexVal
      dsimp only [n] at hilt ⊢
      omega
    · have hindex : b <= iy := by
        apply E.le_iff_le.mp
        change (E b).1 <= (E iy).1
        rw [hEb, hEiy]
        simpa only [hxlast] using hxy'
      have hindexVal : b.val <= iy.val := hindex
      have hilt := iy.isLt
      dsimp only [b] at hindexVal
      dsimp only [n] at hilt ⊢
      omega
  simp only [lpReplicaOrbitCanonicalLastTwoSlots, Finset.mem_insert,
    Finset.mem_singleton]
  rcases hiy with hiy | hiy
  · left
    have hiya : iy = a := Fin.ext hiy
    rw [<- hEa, <- hEiy, hiya]
  · right
    have hiyb : iy = b := Fin.ext hiy
    rw [<- hEb, <- hEiy, hiyb]




noncomputable def LPReplicaOffdiagCanonicalLastTwoPairedCutRealizable
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) : Prop :=
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  ∃ (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
      (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
      (hm : lpReplicaSymmetrizedProfile G sites m = q)
      (hgate : LPReplicaRowGate G sites m B ∅ tag)
      (L : LPReplicaProfileOrbitLabel G sites q m)
      (cut : LPReplicaCoupledPairedCut G sites m B tag),
    lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag =
        lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z ∧
      lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L cut.selector =
        lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard ∧
      let D := cut.half ∆
        cut.half.map lpReplicaCurrentReflect.toEmbedding
      D = Sj ∆ T ∨ D = Si ∆ T





noncomputable def LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) : Prop :=
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let hfixed : B.map lpReplicaCurrentReflect.toEmbedding = B := by
    simpa only [B] using
      lpReplicaCurrentReflect_offdiagSource G sites i j
  let d := lpReplicaDecoratedOrbitAtomFixedRowGateData
    G sites ∅ B q hfixed z
  ∃ cut : LPReplicaRightCoupledPairedCut G sites z.1.1.1 B d.1,
    lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 cut.selector =
      lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard ∧
    let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
    D = Si ∨ D = Sj



theorem lpReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable_false
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    ¬ LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable
      G sites i j q hcard z := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let hfixed : B.map lpReplicaCurrentReflect.toEmbedding = B := by
    simpa only [B] using
      lpReplicaCurrentReflect_offdiagSource G sites i j
  let d := lpReplicaDecoratedOrbitAtomFixedRowGateData
    G sites ∅ B q hfixed z
  intro hrealize
  change ∃ cut : LPReplicaRightCoupledPairedCut
      G sites z.1.1.1 B d.1,
    lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 cut.selector =
      lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard ∧
    (let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
     D = Si ∨ D = Sj) at hrealize
  obtain ⟨cut, _, hD⟩ := hrealize
  rcases hD with hD | hD
  · exact cut.doubledHalf_ne_seamSource
      G sites z.1.1.1 B d.1 i hD
  · exact cut.doubledHalf_ne_seamSource
      G sites z.1.1.1 B d.1 j hD




noncomputable def
    lpReplicaOffdiagCoupledPairedCrossToggleInjectionOfFixedMaskRealizations
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (hrealize : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
        LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2 =
            lpReplicaOrbitFourColorSlotCrossToggle G sites q P
              (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
    LPReplicaOffdiagCoupledPairedCrossToggleInjection G sites i j q where
  selector := fun _ => P
  output := fun z => Classical.choose (hrealize z)
  output_valid := fun z => (Classical.choose_spec (hrealize z)).1
  output_state := fun z => (Classical.choose_spec (hrealize z)).2
  collision_stable := by
    intro z w _
    rfl



theorem lpReplicaOffdiagCoupledPairedCut_leftTarget
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) ∅ tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaCoupledPairedCut G sites m
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) tag)
    (hD : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
    (hA : (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) ∆
        (cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding) =
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) :
    ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCommonSlotsOfCopies
              G sites q m hm L cut.selector)
            (lpReplicaOrbitFourColorSlotStateOfTag
              G sites q m hm L tag) := by
  let y : LPReplicaOffdiagDecoratedTarget G sites i j q :=
    Sum.inl (lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast G sites m q
      _ _ _ tag hm hgate L cut hA hD)
  refine ⟨y, ?_, ?_⟩
  · dsimp only [LPReplicaOffdiagCoupledPairedOutput]
    left
    exact ⟨m, tag, hm, hgate, L, cut, hD, hA, rfl⟩
  · change lpReplicaOrientedFourColorSlotState G sites _ _ q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites _ _ q
          (lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast G sites m q
            _ _ _ tag hm hgate L cut hA hD)) = _
    exact lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast_slotState
      G sites m q _ _ _ tag hm hgate L cut hA hD



theorem lpReplicaOffdiagCoupledPairedCut_rightTarget
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) ∅ tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaCoupledPairedCut G sites m
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) tag)
    (hD : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
    (hA : (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) ∆
        (cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding) =
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j) :
    ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCommonSlotsOfCopies
              G sites q m hm L cut.selector)
            (lpReplicaOrbitFourColorSlotStateOfTag
              G sites q m hm L tag) := by
  let y : LPReplicaOffdiagDecoratedTarget G sites i j q :=
    Sum.inr (lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast G sites m q
      _ _ _ tag hm hgate L cut hA hD)
  refine ⟨y, ?_, ?_⟩
  · dsimp only [LPReplicaOffdiagCoupledPairedOutput]
    right
    exact ⟨m, tag, hm, hgate, L, cut, hD, hA, rfl⟩
  · change lpReplicaOrientedFourColorSlotState G sites _ _ q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites _ _ q
          (lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast G sites m q
            _ _ _ tag hm hgate L cut hA hD)) = _
    exact lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast_slotState
      G sites m q _ _ _ tag hm hgate L cut hA hD



theorem lpReplicaOffdiagCanonicalLastTwoPairedCutRealizable_target
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hrealize : LPReplicaOffdiagCanonicalLastTwoPairedCutRealizable
      G sites i j q hcard z) :
    ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard)
            (lpReplicaOffdiagDecoratedSourceSlotState
              G sites i j q z) := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  change ∃ (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
      (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
      (hm : lpReplicaSymmetrizedProfile G sites m = q)
      (hgate : LPReplicaRowGate G sites m B ∅ tag)
      (L : LPReplicaProfileOrbitLabel G sites q m)
      (cut : LPReplicaCoupledPairedCut G sites m B tag),
    lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag =
        lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z ∧
      lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L cut.selector =
        lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard ∧
      (let D := cut.half ∆
        cut.half.map lpReplicaCurrentReflect.toEmbedding
       D = Sj ∆ T ∨ D = Si ∆ T) at hrealize
  obtain ⟨m, tag, hm, hgate, L, cut, hsource, hmask, hboundary⟩ := hrealize
  let D := cut.half ∆
    cut.half.map lpReplicaCurrentReflect.toEmbedding
  change D = Sj ∆ T ∨ D = Si ∆ T at hboundary
  rcases hboundary with hD | hD
  · have hA : B ∆ D = Si := by
      rw [hD]
      simp [B, symmDiff_assoc, symmDiff_comm, symmDiff_left_comm]
    obtain ⟨y, hy, hstate⟩ := lpReplicaOffdiagCoupledPairedCut_leftTarget
      G sites i j q m tag hm hgate L cut hD hA
    refine ⟨y, hy, ?_⟩
    rw [hstate, hmask, hsource]
  · have hA : B ∆ D = Sj := by
      rw [hD]
      simp [B, symmDiff_assoc, symmDiff_comm, symmDiff_left_comm]
    obtain ⟨y, hy, hstate⟩ := lpReplicaOffdiagCoupledPairedCut_rightTarget
      G sites i j q m tag hm hgate L cut hD hA
    refine ⟨y, hy, ?_⟩
    rw [hstate, hmask, hsource]

set_option maxHeartbeats 800000 in



theorem lpReplicaOffdiagRightCoupledPairedCut_leftTarget
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (hgate : LPReplicaRowGate G sites m ∅ B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag)
    (hA : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding =
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
    (hD : B ∆ (cut.half ∆
        cut.half.map lpReplicaCurrentReflect.toEmbedding) =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) :
    ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q y).2 =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitCommonSlotsOfCopies
            G sites q m hm L cut.selector)
          (lpReplicaOrbitFourColorSlotStateOfTag
            G sites q m hm L tag) := by
  refine ⟨Sum.inl
    (lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast
      G sites m q B
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
        tag hm hB hgate L cut hA hD), ?_⟩
  exact lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast_slotState
    G sites m q B
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      tag hm hB hgate L cut hA hD

set_option maxHeartbeats 800000 in



theorem lpReplicaOffdiagRightCoupledPairedCut_rightTarget
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (hgate : LPReplicaRowGate G sites m ∅ B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag)
    (hA : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding =
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
    (hD : B ∆ (cut.half ∆
        cut.half.map lpReplicaCurrentReflect.toEmbedding) =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) :
    ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q y).2 =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitCommonSlotsOfCopies
            G sites q m hm L cut.selector)
          (lpReplicaOrbitFourColorSlotStateOfTag
            G sites q m hm L tag) := by
  refine ⟨Sum.inr
    (lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast
      G sites m q B
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
        tag hm hB hgate L cut hA hD), ?_⟩
  exact lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast_slotState
    G sites m q B
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      tag hm hB hgate L cut hA hD

set_option maxHeartbeats 4000000 in



theorem lpReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable_target
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hrealize : LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable
      G sites i j q hcard z) :
    ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q y).2 =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard)
          (lpReplicaOffdiagDecoratedSourceSlotState
            G sites i j q z) := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let hfixed : B.map lpReplicaCurrentReflect.toEmbedding = B := by
    simpa only [B] using
      lpReplicaCurrentReflect_offdiagSource G sites i j
  let d := lpReplicaDecoratedOrbitAtomFixedRowGateData
    G sites ∅ B q hfixed z
  change ∃ cut : LPReplicaRightCoupledPairedCut
      G sites z.1.1.1 B d.1,
    lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 cut.selector =
      lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard ∧
    (let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
     D = Si ∨ D = Sj) at hrealize
  obtain ⟨cut, hmask, hboundary⟩ := hrealize
  have hsource :=
    lpReplicaOffdiagDecoratedSourceSlotState_fixedRowGateData
      G sites i j q z
  let D := cut.half ∆
    cut.half.map lpReplicaCurrentReflect.toEmbedding
  change D = Si ∨ D = Sj at hboundary
  rcases hboundary with hD | hD
  · have htarget : B ∆ D = Sj ∆ T := by
      rw [hD]
      simp [B, symmDiff_assoc, symmDiff_comm, symmDiff_left_comm]
    obtain ⟨y, hstate⟩ := lpReplicaOffdiagRightCoupledPairedCut_leftTarget
      G sites i j q z.1.1.1 B d.1 z.1.1.2 hfixed d.2 z.2.2
        cut hD htarget
    refine ⟨y, ?_⟩
    rw [hstate, hmask, ← hsource]
  · have htarget : B ∆ D = Si ∆ T := by
      rw [hD]
      simp [B, symmDiff_assoc, symmDiff_comm, symmDiff_left_comm]
    obtain ⟨y, hstate⟩ := lpReplicaOffdiagRightCoupledPairedCut_rightTarget
      G sites i j q z.1.1.1 B d.1 z.1.1.2 hfixed d.2 z.2.2
        cut hD htarget
    refine ⟨y, ?_⟩
    rw [hstate, hmask, ← hsource]



noncomputable def
    lpReplicaOffdiagDecoratedOrbitInjectionOfFixedMaskTargetRealizations
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (hrealize : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q P
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
    LPReplicaOffdiagDecoratedOrbitInjection G sites i j q := by
  let move : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q :=
    fun z => Classical.choose (hrealize z)
  refine ⟨move, ?_⟩
  intro z w hmove
  apply lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q
  apply (lpReplicaOrbitFourColorSlotCrossToggle_involutive
    G sites q P).injective
  have htarget : Classical.choose (hrealize z) =
      Classical.choose (hrealize w) := by
    simpa only [move] using hmove
  rw [← (Classical.choose_spec (hrealize z)),
    ← (Classical.choose_spec (hrealize w)), htarget]



theorem lpReplicaOffdiagOrbitAtomCardInequality_of_canonicalLastTwoRightPairedCuts
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (hcuts : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable
        G sites i j q hcard z) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q :=
  lpReplicaOffdiagOrbitAtomCardInequality_of_decoratedInjection
    G sites i j q
      (lpReplicaOffdiagDecoratedOrbitInjectionOfFixedMaskTargetRealizations
        G sites i j q
          (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard)
          (fun z =>
            lpReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable_target
              G sites i j q hcard z (hcuts z)))



theorem LPReplicaOffdiagCoupledPairedCrossToggleInjection.output_injective
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCoupledPairedCrossToggleInjection
      G sites i j q) :
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
    rw [<- s.output_state z, <- s.output_state w, houtput]



theorem lpReplicaOffdiagCoupledPairedOutputCard_of_crossToggleInjection
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCoupledPairedCrossToggleInjection
      G sites i j q) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card := by
  let move : LPReplicaOffdiagDecoratedSource G sites i j q ->
      {y // y ∈ lpReplicaOffdiagCoupledPairedOutputs G sites i j q} :=
    fun z => ⟨s.output z, by
      simp only [lpReplicaOffdiagCoupledPairedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact s.output_valid z⟩
  have hmove : Function.Injective move := by
    intro z w h
    apply s.output_injective G sites i j q
    exact congrArg Subtype.val h
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective move hmove



theorem lpReplicaOffdiagCoupledPairedOutputCard_of_fixedMaskRealizations
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (hrealize : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
        LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2 =
            lpReplicaOrbitFourColorSlotCrossToggle G sites q P
              (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card :=
  lpReplicaOffdiagCoupledPairedOutputCard_of_crossToggleInjection
    G sites i j q
      (lpReplicaOffdiagCoupledPairedCrossToggleInjectionOfFixedMaskRealizations
        G sites i j q P hrealize)



theorem lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalFirstTwoRealizations
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (hrealize : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
        LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2 =
            lpReplicaOrbitFourColorSlotCrossToggle G sites q
              (lpReplicaOrbitCanonicalFirstTwoSlots G sites q hcard)
              (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card :=
  lpReplicaOffdiagCoupledPairedOutputCard_of_fixedMaskRealizations
    G sites i j q
      (lpReplicaOrbitCanonicalFirstTwoSlots G sites q hcard) hrealize




theorem lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalLastTwoRealizations
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (hrealize : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
        LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2 =
            lpReplicaOrbitFourColorSlotCrossToggle G sites q
              (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard)
              (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card :=
  lpReplicaOffdiagCoupledPairedOutputCard_of_fixedMaskRealizations
    G sites i j q
      (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard) hrealize



theorem lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalLastTwoPairedCuts
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (hcuts : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      LPReplicaOffdiagCanonicalLastTwoPairedCutRealizable
        G sites i j q hcard z) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card :=
  lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalLastTwoRealizations
    G sites i j q hcard fun z =>
      lpReplicaOffdiagCanonicalLastTwoPairedCutRealizable_target
        G sites i j q hcard z (hcuts z)



theorem lpReplicaOffdiagCoupledPairedHall_of_crossToggleInjection
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCoupledPairedCrossToggleInjection
      G sites i j q) :
    LPReplicaOffdiagCoupledPairedHall G sites i j q := by
  rw [lpReplicaOffdiagCoupledPairedHall_iff_outputCard]
  exact lpReplicaOffdiagCoupledPairedOutputCard_of_crossToggleInjection
    G sites i j q s


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedCrossToggleInjection
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCoupledPairedCrossToggleInjection
      G sites i j q) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q :=
  lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedOutputCard
    G sites i j q
      (lpReplicaOffdiagCoupledPairedOutputCard_of_crossToggleInjection
        G sites i j q s)

end

end StatMech.Ising
