/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets










namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveStrictRouteTargetFibersDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



theorem lpReplicaOrbitFourColorSlotEnds_reflectRowToggle_singleton
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOrbitFourColorSlotState G sites q)
    (row : Finset (LPReplicaOrbitCommonSlot G sites q))
    (d x : LPReplicaOrbitCommonSlot G sites q)
    (hd : exists e, d = Sum.inr e) :
    lpReplicaOrbitFourColorSlotEnds G sites q
        (lpReplicaOrbitFourColorSlotReflectRowToggle G sites q {d} row s) x =
      if x = d then
        Sym2.map lpReplicaCurrentReflect
          (lpReplicaOrbitFourColorSlotEnds G sites q s x)
      else lpReplicaOrbitFourColorSlotEnds G sites q s x := by
  classical
  rcases hd with ⟨⟨de, dk⟩, rfl⟩
  rcases x with fixed | ⟨se, sk⟩
  · simp [lpReplicaOrbitFourColorSlotEnds,
      lpReplicaOrbitFourColorSlotReflectRowToggle,
      lpReplicaOrbitFourColorSlotRowToggle,
      lpReplicaOrbitFourColorSlotReflect,
      lpReplicaOrbitFourColorSlotEdge]
  · unfold lpReplicaOrbitFourColorSlotEnds
    change
      (lpReplicaOrbitFourColorSlotEdge G sites q
        (lpReplicaOrbitFourColorSlotReflect G sites q {Sum.inr ⟨de, dk⟩} s)
        (Sum.inr ⟨se, sk⟩)).1 = _
    rw [lpReplicaOrbitFourColorSlotEdge_reflect_strict]
    by_cases h : (Sum.inr ⟨se, sk⟩ :
        LPReplicaOrbitCommonSlot G sites q) = Sum.inr ⟨de, dk⟩
    · have hsd : (⟨se, sk⟩ :
          Σ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites), Fin (q e.1)) =
            ⟨de, dk⟩ := Sum.inr.inj h
      cases hsd
      have hmem : (Sum.inr ⟨de, dk⟩ :
          LPReplicaOrbitCommonSlot G sites q) ∈
          ({Sum.inr ⟨de, dk⟩} :
            Finset (LPReplicaOrbitCommonSlot G sites q)) :=
        Finset.mem_singleton_self _
      rw [if_pos hmem]
      split
      · exact lpReplicaCurrentEdgeReflect_val G sites _
      · rename_i hne
        exact False.elim (hne rfl)
    · have hnmem : (Sum.inr ⟨se, sk⟩ :
          LPReplicaOrbitCommonSlot G sites q) ∉
          ({Sum.inr ⟨de, dk⟩} :
            Finset (LPReplicaOrbitCommonSlot G sites q)) := by
        intro hmem
        exact h (Finset.mem_singleton.mp hmem)
      rw [if_neg hnmem]
      split
      · rename_i heq
        exact False.elim (h heq)
      · rfl



def LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (d : LPReplicaOrbitCommonSlot G sites q) : Prop :=
  let state := lpReplicaAggregateDecoratedTargetSlotState G sites q y
  let row := lpReplicaOrbitFourColorSlotRowMask G sites q state
  let ends := lpReplicaOrbitFourColorSlotEnds G sites q state
  ¬ (lpReplicaOrbitFoldedSlotEnds G sites q d).IsDiag ∧
    d ∈ row ∧
      ∀ x ∈ ends d, ∃ e ∈ row, e ≠ d ∧ x ∈ ends e



theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_rowMask
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z)) :
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaAggregateDecoratedTargetSlotState G sites q
          (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
            G sites hsite q hcard z d)) =
      Finset.univ \
        {lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateRowSlot
          G sites hsite q z} := by
  classical
  rw [
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_singletons,
    lpReplicaOrbitFourColorSlotRowMask_reflectRowToggle,
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_rowMask_eq_univ
      G sites hsite q hcard z]
  ext x
  simp [Finset.mem_symmDiff]



theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotEnds
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z))
    (x : LPReplicaOrbitCommonSlot G sites q) :
    let a := z.toAggregate G sites q
    let sourceState := lpReplicaOffdiagDecoratedSourceSlotState
      G sites a.1 a.2.1 q a.2.2.2
    let spatial :=
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
        G sites hsite q z d
    lpReplicaOrbitFourColorSlotEnds G sites q
        (lpReplicaAggregateDecoratedTargetSlotState G sites q
          (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
            G sites hsite q hcard z d)) x =
      if x = spatial then
        Sym2.map lpReplicaCurrentReflect
          (lpReplicaOrbitFourColorSlotEnds G sites q sourceState x)
      else lpReplicaOrbitFourColorSlotEnds G sites q sourceState x := by
  classical
  dsimp only
  rw [
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_singletons]
  apply lpReplicaOrbitFourColorSlotEnds_reflectRowToggle_singleton
  let a := z.toAggregate G sites q
  have hdData :=
    (mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff
      G sites hsite q z d.1).mp d.2
  dsimp only at hdData
  exact lpReplicaProfileCopyEquivCommonSlot_eq_inr_of_folded_not_diag
    G sites q a.2.2.2.1.1.1 a.2.2.2.1.1.2 a.2.2.2.2.2 d.1
      hdData.2.2.2



theorem lpReplicaOffdiagDecoratedSourceSlotEnds_copy
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (c : Copy (lpReplicaCurrentGraph G sites) z.1.1.1) :
    lpReplicaOrbitFourColorSlotEnds G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
        (lpReplicaProfileCopyEquivCommonSlot
          G sites q z.1.1.1 z.1.1.2 z.2.2 c) =
      endsM (lpReplicaCurrentGraph G sites) z.1.1.1 c := by
  rw [lpReplicaOffdiagDecoratedSourceSlotState_eq_rowGateData]
  exact lpReplicaOrbitFourColorSlotEnds_stateOfTag_copy
    G sites q z.1.1.1 z.1.1.2 z.2.2 _ c

set_option maxHeartbeats 4000000 in



theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_spatialWitness
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z)) :
    LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness G sites q
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
        G sites hsite q hcard z d)
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
        G sites hsite q z d) := by
  classical
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  let c :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
      G sites hsite q z
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q
    a.2.2.2.1.1.1 a.2.2.2.1.1.2 a.2.2.2.2.2
  let spatial :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
      G sites hsite q z d
  let row :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateRowSlot
      G sites hsite q z
  let route :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
      G sites hsite q hcard z d
  have hdData :=
    (mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff
      G sites hsite q z d.1).mp d.2
  dsimp only at hdData
  have hdK := Finset.mem_sdiff.mp hdData.1
  have hrouteD :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_d
      G sites hsite q hcard z d
  have hfoldD : lpReplicaCurrentFoldedEdge G sites d.1.1 =
      s(Sum.inl (sites route.u), Sum.inl (sites route.v)) := by
    rw [← hrouteD]
    exact route.hfold
  have hc : c.1.1 = lpReplicaCurrentSeamEdge sites k :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy_edge
      G sites hsite q z
  have hpm :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_perfectMatching_of_seamCopy
      G sites hsite q hcard z c hc
  dsimp only at hpm
  obtain ⟨_hKcard, _hsources, hsupport, hunique⟩ := hpm
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  have hreflectedSupport : ∀ x ∈
      endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d.1,
      lpReplicaCurrentReflect x ∈
        lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k :=
    lpReplica_strictPhysicalRoute_reflected_endpoint_mem_tripleSource
      G sites hsite hij hik hjk route.hu route.hv route.huv
        a.2.2.2.1.1.1 d.1 hfoldD
  have hdisjoint := lpReplica_strictPhysicalRoute_disjoint_reflected_ends
    G sites hsite route.huv a.2.2.2.1.1.1 d.1
      hfoldD
  unfold LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · change ¬ (lpReplicaOrbitFoldedSlotEnds G sites q (E d.1)).IsDiag
    rw [lpReplicaOrbitFoldedSlotEnds_copy]
    exact hdData.2.2.2
  · rw [
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_rowMask]
    change E d.1 ∈ Finset.univ \ {E c}
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    exact hdK.2 (Finset.mem_singleton.mpr (E.injective
      (Finset.mem_singleton.mp hmem)))
  · intro x hx
    have hx' := hx
    rw [
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotEnds]
      at hx'
    change x ∈ (if spatial = spatial then
      Sym2.map lpReplicaCurrentReflect
        (lpReplicaOrbitFourColorSlotEnds G sites q
          (lpReplicaOffdiagDecoratedSourceSlotState
            G sites a.1 a.2.1 q a.2.2.2) spatial)
      else _) at hx'
    rw [if_pos rfl] at hx'
    have hspatial : spatial = E d.1 := rfl
    rw [hspatial, lpReplicaOffdiagDecoratedSourceSlotEnds_copy] at hx'
    rw [Sym2.mem_map] at hx'
    obtain ⟨y, hyd, hry⟩ := hx'
    have hxB : x ∈ lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k := by
      rw [← hry]
      exact hreflectedSupport y hyd
    obtain ⟨e, ⟨heK, hxe⟩, _huniqueE⟩ := hunique x hxB
    have heK' := Finset.mem_sdiff.mp heK
    have hed : e ≠ d.1 := by
      intro hed
      subst e
      apply Finset.disjoint_left.mp hdisjoint
      · exact hxe
      · exact Sym2.mem_toFinset.mpr
          (by rw [Sym2.mem_map]; exact ⟨y, hyd, hry⟩)
    refine ⟨E e, ?_, E.injective.ne hed, ?_⟩
    · rw [
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_rowMask]
      change E e ∈ Finset.univ \ {E c}
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hmem
      exact heK'.2 (Finset.mem_singleton.mpr (E.injective
        (Finset.mem_singleton.mp hmem)))
    · rw [
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotEnds]
      change x ∈ (if E e = spatial then _ else
        lpReplicaOrbitFourColorSlotEnds G sites q
          (lpReplicaOffdiagDecoratedSourceSlotState
            G sites a.1 a.2.1 q a.2.2.2) (E e))
      rw [if_neg (fun h => hed (E.injective (h.trans (by rfl))))]
      rw [lpReplicaOffdiagDecoratedSourceSlotEnds_copy]
      exact Sym2.mem_toFinset.mp hxe

set_option maxHeartbeats 6000000 in



theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidate_of_spatialWitness
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z))
    (x : LPReplicaOrbitCommonSlot G sites q)
    (hx : LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
      G sites q
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z d) x) :
    ∃ e : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z),
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
        G sites hsite q z e = x := by
  classical
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  let c :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
      G sites hsite q z
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q
    a.2.2.2.1.1.1 a.2.2.2.1.1.2 a.2.2.2.2.2
  let spatial :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateSpatialSlot
      G sites hsite q z d
  by_cases hxd : x = spatial
  · exact ⟨d, hxd.symm⟩
  have hdData :=
    (mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff
      G sites hsite q z d.1).mp d.2
  dsimp only at hdData
  have hc : c.1.1 = lpReplicaCurrentSeamEdge sites k :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy_edge
      G sites hsite q z
  have hpm :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_perfectMatching_of_seamCopy
      G sites hsite q hcard z c hc
  dsimp only at hpm
  obtain ⟨_hKcard, _hsources, hsupport, hunique⟩ := hpm
  unfold LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness at hx
  dsimp only at hx
  obtain ⟨hxPhysical, hxRow, hxDouble⟩ := hx
  let e := E.symm x
  have hEe : E e = x := E.apply_symm_apply x
  have slot_mem_K {t : LPReplicaOrbitCommonSlot G sites q}
      (ht : t ∈ lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaAggregateDecoratedTargetSlotState G sites q
          (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
            G sites hsite q hcard z d))) :
      E.symm t ∈ Finset.univ \ {c} := by
    rw [
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_rowMask]
      at ht
    have ht' := Finset.mem_sdiff.mp ht
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    have htc : t = E c := by
      rw [← E.apply_symm_apply t]
      exact congrArg E (Finset.mem_singleton.mp hmem)
    exact ht'.2 (Finset.mem_singleton.mpr htc)
  have heK : e ∈ Finset.univ \ {c} := slot_mem_K hxRow
  have htargetEndsX :
      lpReplicaOrbitFourColorSlotEnds G sites q
          (lpReplicaAggregateDecoratedTargetSlotState G sites q
            (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
              G sites hsite q hcard z d)) x =
        endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 e := by
    rw [
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotEnds]
    rw [if_neg hxd]
    rw [← hEe, lpReplicaOffdiagDecoratedSourceSlotEnds_copy]
  have hxSubset : ∀ p ∈ endsM (lpReplicaCurrentGraph G sites)
      a.2.2.2.1.1.1 e,
      p ∈ lpReplicaOrbitFourColorSlotEnds G sites q
        (lpReplicaAggregateDecoratedTargetSlotState G sites q
          (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
            G sites hsite q hcard z d)) spatial := by
    intro p hp
    have hpTarget : p ∈ lpReplicaOrbitFourColorSlotEnds G sites q
        (lpReplicaAggregateDecoratedTargetSlotState G sites q
          (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
            G sites hsite q hcard z d)) x := by
      rw [htargetEndsX]
      exact hp
    obtain ⟨t, htRow, htx, hpt⟩ := hxDouble p hpTarget
    by_cases htd : t = spatial
    · simpa [htd] using hpt
    · let f := E.symm t
      have hEf : E f = t := E.apply_symm_apply t
      have hfK : f ∈ Finset.univ \ {c} := slot_mem_K htRow
      have htargetEndsT :
          lpReplicaOrbitFourColorSlotEnds G sites q
              (lpReplicaAggregateDecoratedTargetSlotState G sites q
                (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
                  G sites hsite q hcard z d)) t =
            endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 f := by
        rw [
          lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotEnds]
        rw [if_neg htd]
        rw [← hEf, lpReplicaOffdiagDecoratedSourceSlotEnds_copy]
      have hpf : p ∈ endsM (lpReplicaCurrentGraph G sites)
          a.2.2.2.1.1.1 f := by
        rw [← htargetEndsT]
        exact hpt
      have hpB : p ∈ lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k := by
        rw [← hsupport]
        exact Finset.mem_biUnion.mpr
          ⟨e, heK, Sym2.mem_toFinset.mpr hp⟩
      obtain ⟨g, hg, huniqueG⟩ := hunique p hpB
      have hef : e = f :=
        (huniqueG e ⟨heK, Sym2.mem_toFinset.mpr hp⟩).trans
          (huniqueG f ⟨hfK, Sym2.mem_toFinset.mpr hpf⟩).symm
      apply False.elim
      apply htx
      rw [← hEe, ← hEf, hef]
  have heGhost0 : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉
      endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 e := by
    intro hghost
    have hghostD := hxSubset lpReplicaCurrentGhost0 hghost
    rw [
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotEnds]
      at hghostD
    rw [if_pos rfl] at hghostD
    have hspatial : spatial = E d.1 := rfl
    rw [hspatial, lpReplicaOffdiagDecoratedSourceSlotEnds_copy,
      Sym2.mem_map] at hghostD
    obtain ⟨y, hyd, hry⟩ := hghostD
    have hy : y = (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) := by
      calc
        y = lpReplicaCurrentReflect (lpReplicaCurrentReflect y) :=
          (lpReplicaCurrentReflect_involutive y).symm
        _ = lpReplicaCurrentReflect lpReplicaCurrentGhost0 :=
          congrArg lpReplicaCurrentReflect hry
        _ = lpReplicaCurrentGhost1 := by
          rfl
    exact hdData.2.2.1 (by simpa [hy] using hyd)
  have heGhost1 : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
      endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 e := by
    intro hghost
    have hghostD := hxSubset lpReplicaCurrentGhost1 hghost
    rw [
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotEnds]
      at hghostD
    rw [if_pos rfl] at hghostD
    have hspatial : spatial = E d.1 := rfl
    rw [hspatial, lpReplicaOffdiagDecoratedSourceSlotEnds_copy,
      Sym2.mem_map] at hghostD
    obtain ⟨y, hyd, hry⟩ := hghostD
    have hy : y = (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) := by
      calc
        y = lpReplicaCurrentReflect (lpReplicaCurrentReflect y) :=
          (lpReplicaCurrentReflect_involutive y).symm
        _ = lpReplicaCurrentReflect lpReplicaCurrentGhost1 :=
          congrArg lpReplicaCurrentReflect hry
        _ = lpReplicaCurrentGhost0 := by
          rfl
    exact hdData.2.1 (by simpa [hy] using hyd)
  have hePhysical : ¬ (lpReplicaCurrentFoldedEdge G sites e.1).IsDiag := by
    intro heDiag
    apply hxPhysical
    rw [← hEe, lpReplicaOrbitFoldedSlotEnds_copy]
    exact heDiag
  have heCandidate : e ∈
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z := by
    apply
      (mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff
        G sites hsite q z e).mpr
    dsimp only
    exact ⟨heK, heGhost0, heGhost1, hePhysical⟩
  refine ⟨⟨e, heCandidate⟩, ?_⟩
  exact hEe

end

end StatMech.Ising
