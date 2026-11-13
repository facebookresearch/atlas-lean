/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Combinatorics.Hall.Basic
import Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange










open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaPairedCutMatchingDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



noncomputable def lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B A Dtarget : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaCoupledPairedCut G sites m B tag)
    (hA : B ∆ (cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding) = A)
    (hD : cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding = Dtarget) :
    LPReplicaDecoratedOrbitAtom G sites A Dtarget q := by
  let y := lpReplicaDecoratedOrbitAtomOfCoupledPairedCut
    G sites m q B tag horbit hgate L cut
  let D := cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding
  change LPReplicaDecoratedOrbitAtom G sites
    (B ∆ D) D q at y
  let yA : LPReplicaDecoratedOrbitAtom G sites A D q :=
    cast (congrArg
      (fun X => LPReplicaDecoratedOrbitAtom G sites X D q) hA) y
  exact cast (congrArg
    (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) hD) yA




noncomputable def lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B A Dtarget : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (hgate : LPReplicaRowGate G sites m ∅ B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag)
    (hA : cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding = A)
    (hD : B ∆ (cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding) = Dtarget) :
    LPReplicaDecoratedOrbitAtom G sites A Dtarget q := by
  let y := lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut
    G sites m q B tag horbit hB hgate L cut
  let D := cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding
  change LPReplicaDecoratedOrbitAtom G sites D (B ∆ D) q at y
  let yA : LPReplicaDecoratedOrbitAtom G sites A (B ∆ D) q :=
    cast (congrArg
      (fun X => LPReplicaDecoratedOrbitAtom G sites X (B ∆ D) q) hA) y
  exact cast (congrArg
    (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) hD) yA




def LPReplicaOffdiagCoupledPairedOutput
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
  let B := Si ∆ Sj ∆ T
  (∃ (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
      (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
      (horbit : lpReplicaSymmetrizedProfile G sites m = q)
      (hgate : LPReplicaRowGate G sites m B ∅ tag)
      (L : LPReplicaProfileOrbitLabel G sites q m)
      (cut : LPReplicaCoupledPairedCut G sites m B tag)
      (hD : cut.half ∆
        cut.half.map lpReplicaCurrentReflect.toEmbedding = Sj ∆ T)
      (hA : B ∆ (cut.half ∆
        cut.half.map lpReplicaCurrentReflect.toEmbedding) = Si),
      y = Sum.inl
        (lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast
          G sites m q B Si (Sj ∆ T) tag horbit hgate L cut hA hD)) ∨
    (∃ (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
      (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
      (horbit : lpReplicaSymmetrizedProfile G sites m = q)
      (hgate : LPReplicaRowGate G sites m B ∅ tag)
      (L : LPReplicaProfileOrbitLabel G sites q m)
      (cut : LPReplicaCoupledPairedCut G sites m B tag)
      (hD : cut.half ∆
        cut.half.map lpReplicaCurrentReflect.toEmbedding = Si ∆ T)
      (hA : B ∆ (cut.half ∆
        cut.half.map lpReplicaCurrentReflect.toEmbedding) = Sj),
      y = Sum.inr
        (lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast
          G sites m q B Sj (Si ∆ T) tag horbit hgate L cut hA hD))


def lpReplicaOffdiagDecoratedTargetOrbitLabel
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) ->
      LPReplicaProfileOrbitLabel G sites q
        (lpReplicaOffdiagDecoratedTargetProfile G sites i j q y)
  | Sum.inl y => y.2.2
  | Sum.inr y => y.2.2


def LPReplicaOffdiagCoupledPairedMatch
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) : Prop :=
  LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
    LPReplicaProfileOrbitLabelReallocates G sites q z.2.2
      (lpReplicaOffdiagDecoratedTargetOrbitLabel G sites i j q y)



theorem lpReplicaOffdiagCoupledPairedMatch_iff_output
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    LPReplicaOffdiagCoupledPairedMatch G sites i j q z y ↔
      LPReplicaOffdiagCoupledPairedOutput G sites i j q y := by
  constructor
  · exact And.left
  · intro hy
    exact ⟨hy, lpReplicaProfileOrbitLabelReallocates_all G sites q
      z.2.2 (lpReplicaOffdiagDecoratedTargetOrbitLabel G sites i j q y)⟩

noncomputable def lpReplicaOffdiagCoupledPairedNeighbors
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact Finset.univ.filter fun y =>
    LPReplicaOffdiagCoupledPairedMatch G sites i j q z y

noncomputable def lpReplicaOffdiagCoupledPairedOutputs
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact Finset.univ.filter
    (LPReplicaOffdiagCoupledPairedOutput G sites i j q)

noncomputable def lpReplicaOffdiagCoupledPairedOutputsAtProfile
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).filter fun y =>
    lpReplicaOffdiagDecoratedTargetProfile G sites i j q y = m



noncomputable def lpReplicaOffdiagCoupledPairedRelevantProfiles
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) := by
  classical
  exact ((Finset.univ : Finset
      (LPReplicaOffdiagDecoratedSource G sites i j q)).image
        (fun z => z.1.1.1)) ∪
    (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).image
      (lpReplicaOffdiagDecoratedTargetProfile G sites i j q)

theorem lpReplicaOffdiagCoupledPairedSource_card_eq_sum_profileFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) =
      ∑ m ∈ lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q,
        (lpReplicaOffdiagDecoratedSourcesAtProfile G sites i j q m).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagDecoratedSourcesAtProfile] using
    Finset.card_eq_sum_card_fiberwise (by
      intro z hz
      unfold lpReplicaOffdiagCoupledPairedRelevantProfiles
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨z, hz, rfl⟩))

theorem lpReplicaOffdiagCoupledPairedOutputs_card_eq_sum_profileFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card =
      ∑ m ∈ lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q,
        (lpReplicaOffdiagCoupledPairedOutputsAtProfile
          G sites i j q m).card := by
  classical
  simpa only [lpReplicaOffdiagCoupledPairedOutputsAtProfile] using
    Finset.card_eq_sum_card_fiberwise (by
      intro y hy
      unfold lpReplicaOffdiagCoupledPairedRelevantProfiles
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨y, hy, rfl⟩))



structure LPReplicaOffdiagCoupledPairedProfileAllocation
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  flow : ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) ->
    ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Nat
  covers : ∀ m ∈
      lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q,
    (lpReplicaOffdiagDecoratedSourcesAtProfile G sites i j q m).card <=
      ∑ n ∈ lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q,
        flow m n
  capacity : ∀ n ∈
      lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q,
    (∑ m ∈ lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q,
        flow m n) <=
      (lpReplicaOffdiagCoupledPairedOutputsAtProfile
        G sites i j q n).card



theorem lpReplicaOffdiagCoupledPairedOutputCard_of_profileAllocation
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (a : LPReplicaOffdiagCoupledPairedProfileAllocation
      G sites i j q) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card := by
  rw [lpReplicaOffdiagCoupledPairedSource_card_eq_sum_profileFibers,
    lpReplicaOffdiagCoupledPairedOutputs_card_eq_sum_profileFibers]
  let R := lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q
  calc
    (∑ m ∈ R,
        (lpReplicaOffdiagDecoratedSourcesAtProfile
          G sites i j q m).card) <=
        ∑ m ∈ R, ∑ n ∈ R, a.flow m n := by
      exact Finset.sum_le_sum a.covers
    _ = ∑ n ∈ R, ∑ m ∈ R, a.flow m n := by
      rw [Finset.sum_comm]
    _ <= ∑ n ∈ R,
        (lpReplicaOffdiagCoupledPairedOutputsAtProfile
          G sites i j q n).card := by
      exact Finset.sum_le_sum a.capacity

noncomputable def LPReplicaOffdiagCoupledPairedHall
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop := by
  classical
  exact forall S : Finset (LPReplicaOffdiagDecoratedSource G sites i j q),
    S.card <= (S.biUnion
      (lpReplicaOffdiagCoupledPairedNeighbors G sites i j q)).card



theorem lpReplicaOffdiagCoupledPairedHall_of_outputCard
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card
        (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
    LPReplicaOffdiagCoupledPairedHall G sites i j q := by
  classical
  intro S
  by_cases hS : S = ∅
  · simp [hS]
  let good := lpReplicaOffdiagCoupledPairedOutputs G sites i j q
  have hneighbors (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
      lpReplicaOffdiagCoupledPairedNeighbors G sites i j q z = good := by
    ext y
    simp only [lpReplicaOffdiagCoupledPairedNeighbors, good,
      lpReplicaOffdiagCoupledPairedOutputs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact lpReplicaOffdiagCoupledPairedMatch_iff_output G sites i j q z y
  have hnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  have hunion : S.biUnion
      (lpReplicaOffdiagCoupledPairedNeighbors G sites i j q) = good := by
    ext y
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨z, hz, hy⟩
      rwa [hneighbors z] at hy
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



theorem lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedOutputCard
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card
        (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  classical
  have hHall := lpReplicaOffdiagCoupledPairedHall_of_outputCard
    G sites i j q hcard
  obtain ⟨move, hmove, _⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (lpReplicaOffdiagCoupledPairedNeighbors G sites i j q)).mp (by
        simpa only [LPReplicaOffdiagCoupledPairedHall] using hHall)
  apply lpReplicaOffdiagOrbitAtomCardInequality_of_decoratedInjection
  exact ⟨move, hmove⟩



theorem lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedProfileAllocation
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (a : LPReplicaOffdiagCoupledPairedProfileAllocation
      G sites i j q) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  apply lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedOutputCard
  exact lpReplicaOffdiagCoupledPairedOutputCard_of_profileAllocation
    G sites i j q a



theorem lpReplicaAggregateProfileOrbitInequality_of_coupledPairedOutputCards
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hcard : ∀ q i j, i ≠ j ->
      Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
        (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_atomCard
    G sites beta J hf r hbeta hJ hhf hr
  intro q i j hij
  exact lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedOutputCard
    G sites i j q (hcard q i j hij)



theorem lpReplicaAggregateProfileOrbitInequality_of_coupledPairedProfileAllocations
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (halloc : ∀ q i j, i ≠ j ->
      LPReplicaOffdiagCoupledPairedProfileAllocation G sites i j q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_coupledPairedOutputCards
    G sites beta J hf r hbeta hJ hhf hr
  intro q i j hij
  exact lpReplicaOffdiagCoupledPairedOutputCard_of_profileAllocation
    G sites i j q (halloc q i j hij)



theorem lpReplicaMatchingDisconn_le_of_coupledPairedOutputCards
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hcard : ∀ q i j, i ≠ j ->
      Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
        (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    sourcePairDisconnSum H beta Jr ∅ ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnTwo H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <=
      2 * lpMatchingDisconnZero H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnOne H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  apply lpReplicaMatchingDisconn_le_of_profileOrbit
    G sites beta J hf r hbeta hJ hhf hr
  exact lpReplicaAggregateProfileOrbitInequality_of_coupledPairedOutputCards
    G sites beta J hf r hbeta hJ hhf hr hcard



theorem lpReplicaMatchingDisconn_le_of_coupledPairedProfileAllocations
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (halloc : ∀ q i j, i ≠ j ->
      LPReplicaOffdiagCoupledPairedProfileAllocation G sites i j q) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    sourcePairDisconnSum H beta Jr ∅ ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnTwo H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <=
      2 * lpMatchingDisconnZero H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnOne H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  apply lpReplicaMatchingDisconn_le_of_coupledPairedOutputCards
    G sites beta J hf r hbeta hJ hhf hr
  intro q i j hij
  exact lpReplicaOffdiagCoupledPairedOutputCard_of_profileAllocation
    G sites i j q (halloc q i j hij)



theorem lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_coupledPairedProfileAllocations
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (halloc : ∀ q i j, i ≠ j ->
      LPReplicaOffdiagCoupledPairedProfileAllocation G sites i j q) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    (∑ i : I, ∑ j : I,
      lpMatchingFiveCurrentCoefficient H beta Jr
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0 := by
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  have hmatch :=
    lpReplicaMatchingDisconn_le_of_coupledPairedProfileAllocations
      G sites beta J hf r hbeta hJ hhf hr halloc
  dsimp only at hmatch
  apply (lpMatchingFiveCurrentCoefficient_sum_nonpos_iff
    H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by
        simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])).mpr
  rw [lpGhostCurrentSquareGap_eq_emptyDisconn H beta Jr
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by
      simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])]
  exact hmatch

end

end StatMech.Ising
