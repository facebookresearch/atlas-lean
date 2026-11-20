/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitPooledSlotMove
import Code.Ising.LebowitzPfisterReplicaOrbitBalancedSecondTransfer












open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy
open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaPooledGateSplitDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

set_option maxHeartbeats 800000 in



theorem lpReplicaTwoPairRowComponent_partialReflectSource_empty
    (G : SimpleGraph V) (sites : I -> V) (j : I)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hsrc : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m) K =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
    (hdisc : ¬ StatMech.Sharpness.RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) K
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    let C := StatMech.Sharpness.RandomCurrent.compOf
      (endsM (lpReplicaCurrentGraph G sites) m) K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaPartialReflectSource
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) C = ∅ := by
  classical
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let e := endsM H m
  let g0 : LPReplicaCurrentVertex V := lpReplicaCurrentGhost0
  let g1 : LPReplicaCurrentVertex V := lpReplicaCurrentGhost1
  let l := lpReplicaCurrentLeft sites j
  let r := lpReplicaCurrentRight sites j
  let C := StatMech.Sharpness.RandomCurrent.compOf e K g0
  let M := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
    lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
  have heven : Even
      (StatMech.Sharpness.RandomCurrent.compOddVertices e K g0).card :=
    StatMech.Sharpness.RandomCurrent.even_compOddVertices e K
      (fun q _ => endsM_not_isDiag H m q) g0
  have hself : StatMech.Sharpness.RandomCurrent.connK e K g0 g0 :=
    Relation.ReflTransGen.refl
  have hdisc' : ¬ StatMech.Sharpness.RandomCurrent.connK e K g0 g1 := by
    simpa only [e, H, g0, g1] using hdisc
  rw [StatMech.Sharpness.RandomCurrent.compOddVertices_eq_filter_sources,
    hsrc] at heven
  have hM : M = {g0, g1, l, r} := by
    ext x
    simp [M, g0, g1, l, r, lpMatchingSeamSource,
      lpMatchingGhostSource, lpReplicaCurrentLeft,
      lpReplicaCurrentRight, lpReplicaCurrentGhost0,
      lpReplicaCurrentGhost1, Finset.mem_symmDiff]
    aesop
  change Even ((M.filter fun x =>
    StatMech.Sharpness.RandomCurrent.connK e K g0 x).card) at heven
  rw [hM, Finset.card_filter] at heven
  have hg0 : g0 ∉ ({g1, l, r} : Finset (LPReplicaCurrentVertex V)) := by
    simp [g0, g1, l, r, lpReplicaCurrentLeft,
      lpReplicaCurrentRight, lpReplicaCurrentGhost0,
      lpReplicaCurrentGhost1]
  have hg1 : g1 ∉ ({l, r} : Finset (LPReplicaCurrentVertex V)) := by
    simp [g1, l, r, lpReplicaCurrentLeft,
      lpReplicaCurrentRight, lpReplicaCurrentGhost1]
  have hlr : l ∉ ({r} : Finset (LPReplicaCurrentVertex V)) := by
    simp [l, r, lpReplicaCurrentLeft, lpReplicaCurrentRight]
  rw [Finset.sum_insert hg0, Finset.sum_insert hg1,
    Finset.sum_insert hlr, Finset.sum_singleton] at heven
  have hsplit :
      (StatMech.Sharpness.RandomCurrent.connK e K g0 l ∧
          ¬ StatMech.Sharpness.RandomCurrent.connK e K g0 r) ∨
        (¬ StatMech.Sharpness.RandomCurrent.connK e K g0 l ∧
          StatMech.Sharpness.RandomCurrent.connK e K g0 r) := by
    by_cases hl : StatMech.Sharpness.RandomCurrent.connK e K g0 l <;>
      by_cases hr : StatMech.Sharpness.RandomCurrent.connK e K g0 r
    · exfalso
      have hnot : ¬ Even 3 := by norm_num
      exact hnot (by simpa [hself, hdisc', hl, hr] using heven)
    · exact Or.inl ⟨hl, hr⟩
    · exact Or.inr ⟨hl, hr⟩
    · exfalso
      have hnot : ¬ Even 1 := by norm_num
      exact hnot (by simpa [hself, hdisc', hl, hr] using heven)
  have hX : M ∩ C = {g0, l} ∨ M ∩ C = {g0, r} := by
    rcases hsplit with hsplit | hsplit
    · left
      rw [hM]
      ext x
      simp [C, StatMech.Sharpness.RandomCurrent.mem_compOf,
        hself, hdisc', hsplit.1, hsplit.2]
    · right
      rw [hM]
      ext x
      simp [C, StatMech.Sharpness.RandomCurrent.mem_compOf,
        hself, hdisc', hsplit.1, hsplit.2]
  have hdouble : M = (M ∩ C) ∆
      (M ∩ C).map lpReplicaCurrentReflect.toEmbedding := by
    have hmapL : ({g0, l} : Finset (LPReplicaCurrentVertex V)).map
        lpReplicaCurrentReflect.toEmbedding = {g1, r} := by
      ext x
      simp [g0, g1, l, r, lpReplicaCurrentLeft,
        lpReplicaCurrentRight, lpReplicaCurrentGhost0,
        lpReplicaCurrentGhost1]
    have hmapR : ({g0, r} : Finset (LPReplicaCurrentVertex V)).map
        lpReplicaCurrentReflect.toEmbedding = {g1, l} := by
      ext x
      simp [g0, g1, l, r, lpReplicaCurrentLeft,
        lpReplicaCurrentRight, lpReplicaCurrentGhost0,
        lpReplicaCurrentGhost1]
    have hdisjL : Disjoint
        ({g0, l} : Finset (LPReplicaCurrentVertex V)) {g1, r} := by
      simp [g0, g1, l, r, lpReplicaCurrentLeft,
        lpReplicaCurrentRight, lpReplicaCurrentGhost0,
        lpReplicaCurrentGhost1]
    have hdisjR : Disjoint
        ({g0, r} : Finset (LPReplicaCurrentVertex V)) {g1, l} := by
      simp [g0, g1, l, r, lpReplicaCurrentLeft,
        lpReplicaCurrentRight, lpReplicaCurrentGhost0,
        lpReplicaCurrentGhost1]
    have hunionL :
        ({g0, l} : Finset (LPReplicaCurrentVertex V)) ∪ {g1, r} =
          {g0, g1, l, r} := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hunionR :
        ({g0, r} : Finset (LPReplicaCurrentVertex V)) ∪ {g1, l} =
          {g0, g1, l, r} := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rcases hX with hX | hX
    · rw [hX, hmapL, Finset.symmDiff_eq_union hdisjL,
        hunionL, hM]
    · rw [hX, hmapR, Finset.symmDiff_eq_union hdisjR,
        hunionR, hM]
  have hchange := lpReplica_source_symmDiff_partialReflectSource M C
  rw [← hdouble] at hchange
  exact symmDiff_eq_left.mp hchange



theorem lpReplicaRowGate_partialReflect_trueComponent_general
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let K := lpReplicaRowCopies G sites m tag true
    let P := edgeComponent e K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let C := StatMech.Sharpness.RandomCurrent.compOf e K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P))
      A (lpReplicaPartialReflectSource B C)
      (lpReplicaPartialReflectTagRaw G sites m P tag) := by
  classical
  dsimp only
  unfold LPReplicaRowGate at hgate ⊢
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K := lpReplicaRowCopies G sites m tag true
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let C := StatMech.Sharpness.RandomCurrent.compOf e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  have hPsub : P ⊆ K := by
    intro c hc
    change c ∈ edgeComponent e K lpReplicaCurrentGhost0 at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hrows0 : Disjoint
      (lpReplicaRowCopies G sites m tag false)
      (lpReplicaRowCopies G sites m tag true) := by
    rw [Finset.disjoint_left]
    intro c hc0 hc1
    simp only [lpReplicaRowCopies, Finset.mem_filter, Finset.mem_univ,
      true_and] at hc0 hc1
    exact Bool.false_ne_true (hc0.symm.trans hc1)
  have hrows : Disjoint
      (lpReplicaRowCopies G sites m tag false) K := by
    simpa only [K] using hrows0
  have hrow0P : Disjoint
      (lpReplicaRowCopies G sites m tag false) P :=
    hrows.mono Finset.Subset.rfl hPsub
  have hcurrent0P (current : Bool) : Disjoint
      (lpReplicaCurrentCopies G sites m tag false current) P :=
    hrow0P.mono
      (lpReplicaCurrentCopies_subset_rowCopies G sites m tag false current)
      Finset.Subset.rfl
  have hcurrent1 (current : Bool) :
      lpReplicaCurrentCopies G sites m tag true current ⊆ K :=
    lpReplicaCurrentCopies_subset_rowCopies G sites m tag true current
  have hsrc1 (current : Bool) :
      StatMech.Sharpness.RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites)
            (lpReplicaCollisionProfile G sites
              (profileFlux (lpReplicaCurrentGraph G sites) m
                (Finset.univ \ P))
              (profileFlux (lpReplicaCurrentGraph G sites) m P)))
          (lpReplicaPartialReflectCopiesRaw G sites m P
            (lpReplicaCurrentCopies G sites m tag true current)) =
        lpReplicaPartialReflectSource
          (StatMech.Sharpness.RandomCurrent.sources e
            (lpReplicaCurrentCopies G sites m tag true current)) C := by
    exact lpReplicaPartialReflect_rowComponent_subconfig_sources
      G sites m K
        (lpReplicaCurrentCopies G sites m tag true current)
        (hcurrent1 current) lpReplicaCurrentGhost0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lpReplicaCurrentCopies_partialReflectTagRaw]
    rw [lpReplicaPartialReflectCopiesRaw_sources_of_disjoint
      G sites m P _ (hcurrent0P false), hgate.1]
  · rw [lpReplicaCurrentCopies_partialReflectTagRaw]
    rw [lpReplicaPartialReflectCopiesRaw_sources_of_disjoint
      G sites m P _ (hcurrent0P true), hgate.2.1]
  · rw [lpReplicaRowCopies_partialReflectTagRaw]
    exact fun hconn => hgate.2.2.1
      ((lpReplicaPartialReflectCopiesRaw_connK_of_disjoint
        G sites m P _ hrow0P _ _).mp hconn)
  · rw [lpReplicaCurrentCopies_partialReflectTagRaw, hsrc1 false,
      hgate.2.2.2.1]
  · rw [lpReplicaCurrentCopies_partialReflectTagRaw, hsrc1 true,
      hgate.2.2.2.2.1]
    simp [lpReplicaPartialReflectSource]
  · rw [lpReplicaRowCopies_partialReflectTagRaw]
    exact lpReplicaPartialReflect_rowComponent_ghost_disconn
      G sites m K hgate.2.2.2.2.2





theorem lpReplicaRowGate_pooledTargetSplit
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (hgate : LPReplicaRowGate G sites m
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) tag) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let K := lpReplicaRowCopies G sites m tag true
    let P := edgeComponent e K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
      (profileFlux (lpReplicaCurrentGraph G sites) m P)
    let pooled := lpReplicaPooledSelectedSlotStateOfCopies
      G sites m q hm P L
    let repaired := lpReplicaPooledSelectedSlotMove G sites q pooled
    let movedTag := lpReplicaPartialReflectTagRaw G sites m P tag
    repaired.profile = target ∧
      ((lpReplicaPooledSelectedOrbitLabelEquivSlotState
        G sites q).symm repaired).2.2.1 =
          lpReplicaProfileOrbitLabelPartialReflectCopies
            G sites q m hm P L ∧
      LPReplicaRowGate G sites target
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
        ∅ movedTag := by
  dsimp only
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K := lpReplicaRowCopies G sites m tag true
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let C := StatMech.Sharpness.RandomCurrent.compOf e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let M := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
    lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
  have hrows := lpReplicaRowGate_rowSources G sites m Si M tag hgate
  have htransport := lpReplicaRowGate_partialReflect_trueComponent_general
    G sites m Si M tag hgate
  have hempty := lpReplicaTwoPairRowComponent_partialReflectSource_empty
    G sites j m K hrows.2 hgate.2.2.2.2.2
  dsimp only [e, K, P, C, Si, M] at htransport hempty
  refine ⟨?_, ?_, ?_⟩
  · exact (lpReplicaCollisionProfile_compl_eq_partialReflectProfile
      G sites m P).symm
  · rfl
  · rw [hempty] at htransport
    exact htransport



theorem lpReplicaRowGate_pooledFirstSplit
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (hgate : LPReplicaRowGate G sites m ∅
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) tag) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let K := lpReplicaRowCopies G sites m tag true
    let P := edgeComponent e K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
      (profileFlux (lpReplicaCurrentGraph G sites) m P)
    let pooled := lpReplicaPooledSelectedSlotStateOfCopies
      G sites m q hm P L
    let repaired := lpReplicaPooledSelectedSlotMove G sites q pooled
    let movedTag := lpReplicaPartialReflectTagRaw G sites m P tag
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    repaired.profile = target ∧
      ((lpReplicaPooledSelectedOrbitLabelEquivSlotState
        G sites q).symm repaired).2.2.1 =
          lpReplicaProfileOrbitLabelPartialReflectCopies
            G sites q m hm P L ∧
      ((LPReplicaRowGate G sites target ∅ Si movedTag ∧
          (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T) ∨
        (LPReplicaRowGate G sites target ∅ Sj movedTag ∧
          (Si ∆ Sj ∆ T) ∆ Sj = Si ∆ T)) := by
  dsimp only
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K := lpReplicaRowCopies G sites m tag true
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let target := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
    (profileFlux (lpReplicaCurrentGraph G sites) m P)
  refine ⟨?_, ?_, ?_⟩
  · exact (lpReplicaCollisionProfile_compl_eq_partialReflectProfile
      G sites m P).symm
  · rfl
  · simpa only [e, K, P, target] using
      lpReplicaRowGate_partialReflect_offdiag
        G sites hsite hij m tag hgate




theorem lpReplicaRowGate_pooledFirstPairSplit
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (hgate : LPReplicaRowGate G sites m ∅
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) tag) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let K := lpReplicaRowCopies G sites m tag true
    let P := edgeComponent e K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let C := StatMech.Sharpness.RandomCurrent.compOf e K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
      (profileFlux (lpReplicaCurrentGraph G sites) m P)
    let pooled := lpReplicaPooledSelectedSlotStateOfCopies
      G sites m q hm P L
    let repaired := lpReplicaPooledSelectedSlotMove G sites q pooled
    let movedTag := lpReplicaPartialReflectTagRaw G sites m P tag
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    let B := Si ∆ Sj ∆ T
    let X := B ∩ C
    repaired.profile = target ∧
      ((lpReplicaPooledSelectedOrbitLabelEquivSlotState
        G sites q).symm repaired).2.2.1 =
          lpReplicaProfileOrbitLabelPartialReflectCopies
            G sites q m hm P L ∧
      ((LPReplicaRowGate G sites target ∅ Si movedTag ∧
          Sj ∆ T = X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∨
        (LPReplicaRowGate G sites target ∅ Sj movedTag ∧
          Si ∆ T = X ∆ X.map lpReplicaCurrentReflect.toEmbedding)) := by
  dsimp only
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K := lpReplicaRowCopies G sites m tag true
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let C := StatMech.Sharpness.RandomCurrent.compOf e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let X := B ∩ C
  let target := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
    (profileFlux (lpReplicaCurrentGraph G sites) m P)
  have hrows := lpReplicaRowGate_rowSources G sites m ∅ B tag hgate
  have hgateFields := hgate
  unfold LPReplicaRowGate at hgateFields
  have htransport := lpReplicaRowGate_partialReflect_trueComponent
    G sites m B tag hgate
  have halloc := lpReplicaOffdiagRowComponent_partialReflectAllocation
    G sites hsite hij m K hrows.2 hgateFields.2.2.2.2.2
  have hchange := lpReplica_source_symmDiff_partialReflectSource B C
  dsimp only [e, K, P, C, Si, Sj, T, B, X, target] at htransport halloc hchange
  refine ⟨?_, ?_, ?_⟩
  · exact (lpReplicaCollisionProfile_compl_eq_partialReflectProfile
      G sites m P).symm
  · rfl
  · rcases halloc with halloc | halloc
    · left
      refine ⟨by simpa only [halloc.1] using htransport, ?_⟩
      rw [← halloc.2]
      exact hchange
    · right
      refine ⟨by simpa only [halloc.1] using htransport, ?_⟩
      rw [← halloc.2]
      exact hchange

end

end StatMech.Ising
