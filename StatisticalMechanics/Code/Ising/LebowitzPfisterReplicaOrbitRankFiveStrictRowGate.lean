/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveSingletonRowTag








namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveStrictRowGateDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

set_option maxHeartbeats 1600000 in



theorem lpReplicaOffdiagDecoratedSource_strictRoute_target_rowGate
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    {i j k u v : I}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hu : u = i ∨ u = j ∨ u = k)
    (hv : v = i ∨ v = j ∨ v = k) (huv : u ≠ v)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (c d : Copy (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites k)
    (hcd : c ≠ d)
    (hfold : lpReplicaCurrentFoldedEdge G sites d.1 =
      s(Sum.inl (sites u), Sum.inl (sites v)))
    (hdisc :
      let target := lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1
          (Finset.univ \ {d}))
        (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 {d})
      let K' := lpReplicaPartialReflectCopiesRaw
        G sites z.1.1.1 {d} (Finset.univ \ {c})
      ¬ connK (endsM (lpReplicaCurrentGraph G sites) target) K'
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    let l := lpReplicaThirdOfThree i j k u v
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1
        (Finset.univ \ {d}))
      (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 {d})
    let c' := lpReplicaPartialReflectCopyEquivRaw G sites
      z.1.1.1 {d} c
    LPReplicaRowGate G sites target
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) l ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      (lpReplicaSingletonFalseRowTag c') := by
  classical
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let m := z.1.1.1
  let target := lpReplicaCollisionProfile G sites
    (profileFlux H m (Finset.univ \ {d}))
    (profileFlux H m {d})
  let E' := endsM H target
  let R := lpReplicaPartialReflectCopyEquivRaw G sites m {d}
  let c' := R c
  let tag := lpReplicaSingletonFalseRowTag c'
  let Sk := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k
  let Sl := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
      (lpReplicaThirdOfThree i j k u v)
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  have hcnot : c ∉ ({d} : Finset (Copy H m)) := by
    simpa only [Finset.mem_singleton] using hcd
  have hcEdgeFin : c'.1 = c.1 := by
    simpa only [c', R, H, m, if_neg hcnot] using
      (lpReplicaPartialReflectCopyEquivRaw_edge G sites m {d} c)
  have hcEdge : c'.1.1 = lpReplicaCurrentSeamEdge sites k :=
    (congrArg Subtype.val hcEdgeFin).trans hc
  have hcSource : RandomCurrent.sources E' {c'} = Sk := by
    rw [randomCurrent_sources_singleton_eq_ends_toFinset_of_not_isDiag
      E' c' (endsM_not_isDiag (G := H) target c')]
    change c'.1.1.toFinset = Sk
    rw [hcEdge]
    exact lpReplicaCurrentSeamEdge_toFinset_eq_matchingSeamSource sites k
  have hfull : RandomCurrent.sources E' Finset.univ = Sk ∆ Sl ∆ T := by
    simpa only [E', target, H, m, Sk, Sl, T] using
      (lpReplicaOffdiagDecoratedSource_strictRoute_target_fullSources
        G sites hsite hij hik hjk hu hv huv q z d hfold)
  have hrow1Source :
      RandomCurrent.sources E' (Finset.univ \ {c'}) = Sl ∆ T := by
    rw [StatMech.GrahamGHS.FourColor.sources_sdiff_of_subset (by simp),
      hfull, hcSource]
    simp [symmDiff_assoc, symmDiff_left_comm, symmDiff_comm]
  have hrow0False :
      lpReplicaCurrentCopies G sites target tag false false = {c'} := by
    exact lpReplicaCurrentCopies_singletonFalse_false_false
      G sites target c'
  have hrow0True :
      lpReplicaCurrentCopies G sites target tag false true = ∅ := by
    exact lpReplicaCurrentCopies_singletonFalse_false_true
      G sites target c'
  have hrow1False :
      lpReplicaCurrentCopies G sites target tag true false =
        Finset.univ \ {c'} := by
    exact lpReplicaCurrentCopies_singletonFalse_true_false
      G sites target c'
  have hrow1True :
      lpReplicaCurrentCopies G sites target tag true true = ∅ := by
    exact lpReplicaCurrentCopies_singletonFalse_true_true
      G sites target c'
  have hrow0 : lpReplicaRowCopies G sites target tag false = {c'} := by
    exact lpReplicaRowCopies_singletonFalse_false G sites target c'
  have hrow1 : lpReplicaRowCopies G sites target tag true =
      Finset.univ \ {c'} := by
    exact lpReplicaRowCopies_singletonFalse_true G sites target c'
  have himage : lpReplicaPartialReflectCopiesRaw G sites m {d}
      (Finset.univ \ {c}) = Finset.univ \ {c'} := by
    simpa only [c', R] using
      (lpReplicaPartialReflectCopiesRaw_sdiff_singleton G sites m d c)
  have hdisc1 : ¬ connK E' (Finset.univ \ {c'})
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    rw [← himage]
    simpa only [E', target, H, m] using hdisc
  have hdisc0 : ¬ connK E' {c'}
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    simpa only [Finset.union_empty] using
      (lpReplica_seam_union_parallelCopies_ghost_disconnected
        G sites k target c' c' ∅ hcEdge (by simp))
  unfold LPReplicaRowGate
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change RandomCurrent.sources E'
      (lpReplicaCurrentCopies G sites target tag false false) = Sk
    rw [hrow0False]
    exact hcSource
  · change RandomCurrent.sources E'
      (lpReplicaCurrentCopies G sites target tag false true) = ∅
    rw [hrow0True]
    exact randomCurrent_sources_empty E'
  · change ¬ connK E' (lpReplicaRowCopies G sites target tag false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
    rw [hrow0]
    exact hdisc0
  · change RandomCurrent.sources E'
      (lpReplicaCurrentCopies G sites target tag true false) = Sl ∆ T
    rw [hrow1False]
    exact hrow1Source
  · change RandomCurrent.sources E'
      (lpReplicaCurrentCopies G sites target tag true true) = ∅
    rw [hrow1True]
    exact randomCurrent_sources_empty E'
  · change ¬ connK E' (lpReplicaRowCopies G sites target tag true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
    rw [hrow1]
    exact hdisc1

end

end StatMech.Ising
