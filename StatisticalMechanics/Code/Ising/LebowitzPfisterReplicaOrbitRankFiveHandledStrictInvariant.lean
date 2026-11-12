/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow
import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictInvariant
import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall








namespace StatMech.Ising

noncomputable section

open scoped symmDiff

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveHandledStrictInvariantDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



theorem
    lpReplicaAggregateRankFiveStrictRouteCandidates_card_eq_two_of_two_spatialWitnesses
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (x₀ x₁ : LPReplicaOrbitCommonSlot G sites q) (hxx : x₀ ≠ x₁)
    (hx₀ : LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
      G sites q y x₀)
    (hx₁ : LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
      G sites q y x₁)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (hzy : LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z y) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z).card = 2 := by
  classical
  obtain ⟨d, hd⟩ := hzy
  have hx₀' : LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
      G sites q
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z d) x₀ := by
    rw [hd]
    exact hx₀
  have hx₁' : LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
      G sites q
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z d) x₁ := by
    rw [hd]
    exact hx₁
  obtain ⟨e₀, he₀⟩ :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidate_of_spatialWitness
      G sites hsite q hcard z d x₀ hx₀'
  obtain ⟨e₁, he₁⟩ :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidate_of_spatialWitness
      G sites hsite q hcard z d x₁ hx₁'
  have he : e₀ ≠ e₁ := by
    intro h
    apply hxx
    rw [← he₀, ← he₁, h]
  have htwo : 2 ≤
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card := by
    have heVal : e₀.1 ≠ e₁.1 := fun h => he (Subtype.ext h)
    rw [← Finset.card_pair heVal]
    apply Finset.card_le_card
    intro e heMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at heMem
    rcases heMem with rfl | rfl
    · exact e₀.2
    · exact e₁.2
  have hle :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_le_two
      G sites hsite q hcard z
  omega



theorem lpReplicaAggregateDecoratedTargetSlotState_toAggregate
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    lpReplicaAggregateDecoratedTargetSlotState G sites q
        (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q y) =
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q y).2 := by
  cases y <;> rfl

set_option maxHeartbeats 1200000 in



theorem lpReplicaRankFiveMarkedOutputData_hasStrictPhysicalDoubleIncidence_iff
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (d : LPReplicaLowRowMarkedOutputData G sites q z) :
    LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites i j q d.output ↔
      LPReplicaStrictPhysicalDoubleIncidenceRaw G sites z.1.1.1
        (lpReplicaRowCopies G sites z.1.1.1
          (lpReplicaToggleRows G sites z.1.1.1 {d.copy}
            (lpReplicaDecoratedSourceRowGateData G sites i j q z).1) true) := by
  classical
  rcases d.branch with ⟨y, hy, hc⟩ | ⟨y, hy, hc⟩
  · obtain ⟨s, hp, _hL, _hP, hmove, y', _hyBal, hyState, hyPres⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_iSeam
        G sites hsite hij q hcard z hthree d.copy d.copy_active hc
    have hout : d.output = Sum.inl y' := by
      rw [hy]
      apply lpReplicaOffdiagDecoratedTargetBranchedSlotState_injective
        G sites i j q
      apply Prod.ext
      · rfl
      · have hdState := d.state_eq
        rw [hy] at hdState
        exact hdState.trans hyState.symm
    rw [hout, LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence,
      hyPres,
      lpReplicaDecoratedOrbitAtomOfBalancedSelector_left_hasStrictPhysicalDoubleIncidence]
    rcases s with ⟨sp, sorbit, stag, sgate, slabel, sselector,
      sfalse, strue, srow0, srow1⟩
    dsimp at hp hmove ⊢
    subst sp
    rw [eq_of_heq hmove]
  · obtain ⟨s, hp, _hL, _hP, hmove, y', _hyBal, hyState,
      s', hyPres, hp', hselector', htag'⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_jSeam
        G sites hsite hij q hcard z hthree d.copy d.copy_active hc
    have hout : d.output = Sum.inr y' := by
      rw [hy]
      apply lpReplicaOffdiagDecoratedTargetBranchedSlotState_injective
        G sites i j q
      apply Prod.ext
      · rfl
      · have hdState := d.state_eq
        rw [hy] at hdState
        exact hdState.trans hyState.symm
    rw [hout, LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence,
      hyPres,
      lpReplicaDecoratedOrbitAtomOfBalancedSelector_left_hasStrictPhysicalDoubleIncidence]
    rcases s with ⟨sp, sorbit, stag, sgate, slabel, sselector,
      sfalse, strue, srow0, srow1⟩
    rcases s' with ⟨sp', sorbit', stag', sgate', slabel', sselector',
      sfalse', strue', srow0', srow1'⟩
    dsimp at hp hp' hselector' htag' hmove ⊢
    subst sp
    subst sp'
    rw [eq_of_heq hselector', eq_of_heq htag', eq_of_heq hmove]



theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_exists_parallelPhysicalPair
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh :
      let data := lpReplicaDecoratedSourceRowGateData G sites i j q z
      let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false
      K.card = 3 ∧
        ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
    (d : LPReplicaLowRowMarkedOutputData G sites q z)
    (hstrict :
      LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites i j q d.output) :
    let data := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false
    ∃ c e, c ≠ e ∧ Finset.univ \ K = {c, e} ∧
      ¬ (lpReplicaCurrentFoldedEdge G sites c.1).IsDiag := by
  classical
  dsimp only
  have hraw :=
    (lpReplicaRankFiveMarkedOutputData_hasStrictPhysicalDoubleIncidence_iff
      G sites hsite hij q hcard z hhigh.1 d).mp hstrict
  obtain ⟨c, e, hce, hpair, hiff⟩ :=
    lpReplicaOffdiagDecoratedSource_rankFive_nonsaturatedHigh_singletonToggle_raw_iff
      G sites hsite hij q hcard z hhigh d.copy d.copy_active
  exact ⟨c, e, hce, hpair, hiff.mp hraw⟩

set_option maxHeartbeats 1600000 in



theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_two_spatialWitnesses
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh :
      let data := lpReplicaDecoratedSourceRowGateData G sites i j q z
      let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false
      K.card = 3 ∧
        ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
    (d : LPReplicaLowRowMarkedOutputData G sites q z)
    (hstrict :
      LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites i j q d.output) :
    ∃ x₀ x₁ : LPReplicaOrbitCommonSlot G sites q, x₀ ≠ x₁ ∧
      LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness G sites q
        (lpReplicaOffdiagDecoratedTargetToAggregate
          G sites i j q d.output) x₀ ∧
      LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness G sites q
        (lpReplicaOffdiagDecoratedTargetToAggregate
          G sites i j q d.output) x₁ := by
  classical
  let data := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2
  let sourceState := lpReplicaOffdiagDecoratedSourceSlotState
    G sites i j q z
  let target := lpReplicaOffdiagDecoratedTargetToAggregate
    G sites i j q d.output
  obtain ⟨c, e, hce, hpair, hcPhysical⟩ :=
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_exists_parallelPhysicalPair
      G sites hsite hij q hcard z hhigh d hstrict
  have hcC : c ∈ Finset.univ \ K := by
    rw [hpair]
    simp
  have heC : e ∈ Finset.univ \ K := by
    rw [hpair]
    simp
  have hca : c ≠ d.copy := by
    intro h
    exact (Finset.mem_sdiff.mp hcC).2 (h ▸ d.copy_active)
  have hea : e ≠ d.copy := by
    intro h
    exact (Finset.mem_sdiff.mp heC).2 (h ▸ d.copy_active)
  have hparallel : c.1.1 = e.1.1 :=
    lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hhigh.1 c hcC e heC
  have hfixed : d.copy.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites := by
    rcases d.branch with ⟨_y, _hy, hc⟩ | ⟨_y, _hy, hc⟩
    · exact lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam
        G sites i z.1.1.1 d.copy hc
    · exact lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam
        G sites j z.1.1.1 d.copy hc
  have htargetState :
      lpReplicaAggregateDecoratedTargetSlotState G sites q target =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
            z.1.1.2 z.2.2 {d.copy}) sourceState := by
    exact (lpReplicaAggregateDecoratedTargetSlotState_toAggregate
      G sites i j q d.output).trans d.state_eq
  have hreflect : lpReplicaOrbitFourColorSlotReflect G sites q
      (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 {d.copy}) sourceState = sourceState :=
    lpReplicaOrbitFourColorSlotReflect_singletonCopy_of_fixed
      G sites q z.1.1.1 z.1.1.2 z.2.2 d.copy hfixed sourceState
  have hends (x : LPReplicaOrbitCommonSlot G sites q) :
      lpReplicaOrbitFourColorSlotEnds G sites q
          (lpReplicaAggregateDecoratedTargetSlotState G sites q target) x =
        lpReplicaOrbitFourColorSlotEnds G sites q sourceState x := by
    rw [htargetState, lpReplicaOrbitFourColorSlotCrossToggle, hreflect]
    rfl
  have hrow : lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaAggregateDecoratedTargetSlotState G sites q target) =
        Finset.univ \ {E d.copy} := by
    rw [htargetState, lpReplicaOrbitFourColorSlotRowMask_crossToggle,
      lpReplicaOffdiagDecoratedSource_rank_five_highRow_rowMask_eq_univ
        G sites hsite hij q hcard z (Or.inr hhigh)]
    rw [lpReplicaOrbitCommonSlotsOfCopies_singleton]
    change Finset.univ ∆ {E d.copy} = Finset.univ \ {E d.copy}
    ext x
    simp [Finset.mem_symmDiff]
  have hcRow : E c ∈ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaAggregateDecoratedTargetSlotState G sites q target) := by
    rw [hrow]
    simp [hca]
  have heRow : E e ∈ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaAggregateDecoratedTargetSlotState G sites q target) := by
    rw [hrow]
    simp [hea]
  have hEcEe : E c ≠ E e := fun h => hce (E.injective h)
  have hcFold : ¬ (lpReplicaOrbitFoldedSlotEnds G sites q (E c)).IsDiag := by
    rw [lpReplicaOrbitFoldedSlotEnds_copy]
    exact hcPhysical
  have heFold : ¬ (lpReplicaOrbitFoldedSlotEnds G sites q (E e)).IsDiag := by
    rw [lpReplicaOrbitFoldedSlotEnds_copy]
    intro heDiag
    apply hcPhysical
    unfold lpReplicaCurrentFoldedEdge at heDiag ⊢
    rw [hparallel]
    exact heDiag
  have hendsParallel :
      lpReplicaOrbitFourColorSlotEnds G sites q sourceState (E c) =
        lpReplicaOrbitFourColorSlotEnds G sites q sourceState (E e) := by
    rw [lpReplicaOffdiagDecoratedSourceSlotEnds_copy,
      lpReplicaOffdiagDecoratedSourceSlotEnds_copy]
    unfold StatMech.Sharpness.FluxEdgeCopy.endsM
    rw [hparallel]
  refine ⟨E c, E e, hEcEe, ?_, ?_⟩
  · unfold LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
    dsimp only
    refine ⟨hcFold, hcRow, ?_⟩
    intro x hx
    refine ⟨E e, heRow, hEcEe.symm, ?_⟩
    change x ∈ lpReplicaOrbitFourColorSlotEnds G sites q
      (lpReplicaAggregateDecoratedTargetSlotState G sites q target) (E c) at hx
    change x ∈ lpReplicaOrbitFourColorSlotEnds G sites q
      (lpReplicaAggregateDecoratedTargetSlotState G sites q target) (E e)
    rw [hends] at hx
    rw [hends, ← hendsParallel]
    exact hx
  · unfold LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
    dsimp only
    refine ⟨heFold, heRow, ?_⟩
    intro x hx
    refine ⟨E c, hcRow, hEcEe, ?_⟩
    change x ∈ lpReplicaOrbitFourColorSlotEnds G sites q
      (lpReplicaAggregateDecoratedTargetSlotState G sites q target) (E e) at hx
    change x ∈ lpReplicaOrbitFourColorSlotEnds G sites q
      (lpReplicaAggregateDecoratedTargetSlotState G sites q target) (E c)
    rw [hends] at hx
    rw [hends, hendsParallel]
    exact hx



theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_incoming_degree_two
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh :
      let data := lpReplicaDecoratedSourceRowGateData G sites i j q z
      let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false
      K.card = 3 ∧
        ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
    (d : LPReplicaLowRowMarkedOutputData G sites q z)
    (hstrict :
      LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites i j q d.output)
    (w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (hrelated : LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard w
        (lpReplicaOffdiagDecoratedTargetToAggregate
          G sites i j q d.output)) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q w).card = 2 := by
  obtain ⟨x₀, x₁, hxx, hx₀, hx₁⟩ :=
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_two_spatialWitnesses
      G sites hsite hij q hcard z hhigh d hstrict
  exact
    lpReplicaAggregateRankFiveStrictRouteCandidates_card_eq_two_of_two_spatialWitnesses
      G sites hsite q hcard _ x₀ x₁ hxx hx₀ hx₁ w hrelated

set_option maxHeartbeats 8000000 in



theorem
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_injective
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    Function.Injective (fun d :
        ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
          G sites hsite q z) =>
      lpReplicaAggregateDecoratedTargetSlotState G sites q
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z d)) := by
  classical
  intro d e hstate
  let a := z.toAggregate G sites q
  let sourceState := lpReplicaOffdiagDecoratedSourceSlotState
    G sites a.1 a.2.1 q a.2.2.2
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q
    a.2.2.2.1.1.1 a.2.2.2.1.1.2 a.2.2.2.2.2
  let c :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy
      G sites hsite q z
  let routeD :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
      G sites hsite q hcard z d
  let routeE :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate
      G sites hsite q hcard z e
  have hrouteDc : routeD.c = c :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_c
      G sites hsite q hcard z d
  have hrouteEc : routeE.c = c :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_c
      G sites hsite q hcard z e
  have hrouteDd : routeD.d = d.1 :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_d
      G sites hsite q hcard z d
  have hrouteEd : routeE.d = e.1 :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_d
      G sites hsite q hcard z e
  change
    lpReplicaAggregateDecoratedTargetSlotState G sites q
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z d) =
      lpReplicaAggregateDecoratedTargetSlotState G sites q
        (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
          G sites hsite q hcard z e) at hstate
  rw [
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState,
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState]
      at hstate
  have hstate' :
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q
          {E d.1} {E c} sourceState =
        lpReplicaOrbitFourColorSlotReflectRowToggle G sites q
          {E e.1} {E c} sourceState := by
    rw [lpReplicaOrbitCommonSlotsOfCopies_singleton,
      lpReplicaOrbitCommonSlotsOfCopies_singleton,
      lpReplicaOrbitCommonSlotsOfCopies_singleton,
      lpReplicaOrbitCommonSlotsOfCopies_singleton,
      hrouteDc, hrouteEc, hrouteDd, hrouteEd] at hstate
    exact hstate
  have hdData :=
    (mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff
      G sites hsite q z d.1).mp d.2
  have heData :=
    (mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff
      G sites hsite q z e.1).mp e.2
  dsimp only at hdData heData
  have hdStrict : ∃ x, E d.1 = Sum.inr x :=
    lpReplicaProfileCopyEquivCommonSlot_eq_inr_of_folded_not_diag
      G sites q a.2.2.2.1.1.1 a.2.2.2.1.1.2 a.2.2.2.2.2 d.1
        hdData.2.2.2
  have heStrict : ∃ x, E e.1 = Sum.inr x :=
    lpReplicaProfileCopyEquivCommonSlot_eq_inr_of_folded_not_diag
      G sites q a.2.2.2.1.1.1 a.2.2.2.1.1.2 a.2.2.2.2.2 e.1
        heData.2.2.2
  apply Subtype.ext
  apply E.injective
  exact lpReplicaOrbitFourColorSlotReflectRowToggle_strictSingleton_injective
    G sites q sourceState {E c} hdStrict heStrict hstate'



def lpReplicaAggregateDecoratedTargetFlipMultiplicity
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    LPReplicaAggregateDecoratedTarget G sites q :=
  ⟨⟨1 - y.1.val, by omega⟩, y.2⟩

@[simp] theorem lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y ≠ y := by
  intro h
  have hval := congrArg
    (fun z : LPReplicaAggregateDecoratedTarget G sites q => z.1.val) h
  have hy := y.1.isLt
  simp only [lpReplicaAggregateDecoratedTargetFlipMultiplicity] at hval
  omega

@[simp] theorem lpReplicaAggregateDecoratedTargetFlipMultiplicity_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q
        (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) = y := by
  rcases y with ⟨⟨n, hn⟩, tail⟩
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl <;> rfl

@[simp] theorem lpReplicaAggregateDecoratedTargetFlipMultiplicity_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    lpReplicaAggregateDecoratedTargetSlotState G sites q
        (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) =
      lpReplicaAggregateDecoratedTargetSlotState G sites q y := by
  rfl



@[simp] theorem
    lpReplicaAggregateRankFiveStrictRouteTargetSpatialWitness_flip_iff
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (x : LPReplicaOrbitCommonSlot G sites q) :
    LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness G sites q
        (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) x ↔
      LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
        G sites q y x := by
  unfold LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness
  rw [lpReplicaAggregateDecoratedTargetFlipMultiplicity_slotState]



theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_flip_incoming_degree_two
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh :
      let data := lpReplicaDecoratedSourceRowGateData G sites i j q z
      let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false
      K.card = 3 ∧
        ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
    (d : LPReplicaLowRowMarkedOutputData G sites q z)
    (hstrict :
      LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites i j q d.output)
    (w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (hrelated : LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard w
        (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output))) :
    (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q w).card = 2 := by
  obtain ⟨x₀, x₁, hxx, hx₀, hx₁⟩ :=
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_two_spatialWitnesses
      G sites hsite hij q hcard z hhigh d hstrict
  exact
    lpReplicaAggregateRankFiveStrictRouteCandidates_card_eq_two_of_two_spatialWitnesses
      G sites hsite q hcard _ x₀ x₁ hxx
        (lpReplicaAggregateRankFiveStrictRouteTargetSpatialWitness_flip_iff
          G sites q _ x₀ |>.mpr hx₀)
        (lpReplicaAggregateRankFiveStrictRouteTargetSpatialWitness_flip_iff
          G sites q _ x₁ |>.mpr hx₁)
        w hrelated



theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_incomingDegree_one_eq_empty
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh :
      let data := lpReplicaDecoratedSourceRowGateData G sites i j q z
      let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false
      K.card = 3 ∧
        ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
    (d : LPReplicaLowRowMarkedOutputData G sites q z)
    (hstrict :
      LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites i j q d.output) :
    LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 1
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output) = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  obtain ⟨w, hw⟩ := hnonempty
  have hwData :=
    (mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff
      G sites hsite q hcard 1 _ w).mp hw
  have htwo :=
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_incoming_degree_two
      G sites hsite hij q hcard z hhigh d hstrict w hwData.1
  omega


theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_flip_incomingDegree_one_eq_empty
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh :
      let data := lpReplicaDecoratedSourceRowGateData G sites i j q z
      let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false
      K.card = 3 ∧
        ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
    (d : LPReplicaLowRowMarkedOutputData G sites q z)
    (hstrict :
      LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites i j q d.output) :
    LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 1
          (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q
            (lpReplicaOffdiagDecoratedTargetToAggregate
              G sites i j q d.output)) = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  obtain ⟨w, hw⟩ := hnonempty
  have hwData :=
    (mem_LPReplicaAggregateRankFiveStrictRouteIncomingDegree_iff
      G sites hsite q hcard 1 _ w).mp hw
  have htwo :=
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_flip_incoming_degree_two
      G sites hsite hij q hcard z hhigh d hstrict w hwData.1
  omega



theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_targetLoad_eq_half_incomingDegreeTwo
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh :
      let data := lpReplicaDecoratedSourceRowGateData G sites i j q z
      let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false
      K.card = 3 ∧
        ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
    (d : LPReplicaLowRowMarkedOutputData G sites q z)
    (hstrict :
      LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites i j q d.output) :
    (∑ w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight G sites hsite q hcard w
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output)) =
      ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 2
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output)).card : Real) / 2 := by
  rw [LPReplicaAggregateRankFiveStrictRouteWeight_sum_source]
  rw [lpReplicaRankFiveNonsaturatedHighMarkedOutput_incomingDegree_one_eq_empty
    G sites hsite hij q hcard z hhigh d hstrict]
  simp



theorem
    lpReplicaRankFiveNonsaturatedHighMarkedOutput_targetLoad_lt_one_iff
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh :
      let data := lpReplicaDecoratedSourceRowGateData G sites i j q z
      let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false
      K.card = 3 ∧
        ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
    (d : LPReplicaLowRowMarkedOutputData G sites q z)
    (hstrict :
      LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites i j q d.output) :
    (∑ w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight G sites hsite q hcard w
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output)) < 1 ↔
      (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 2
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output)).card ≤ 1 := by
  rw [lpReplicaRankFiveNonsaturatedHighMarkedOutput_targetLoad_eq_half_incomingDegreeTwo
    G sites hsite hij q hcard z hhigh d hstrict]
  constructor
  · intro h
    have hreal : ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 2
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output)).card : Real) < 2 := by
      linarith
    have hnat : (LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 2
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output)).card < 2 := by
      exact_mod_cast hreal
    omega
  · intro h
    have hreal : ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree
        G sites hsite q hcard 2
          (lpReplicaOffdiagDecoratedTargetToAggregate
            G sites i j q d.output)).card : Real) ≤ 1 := by
      exact_mod_cast h
    linarith

@[simp] theorem
    lpReplicaAggregateDecoratedTargetFlipMultiplicity_hasStrictPhysicalDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites q
        (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) ↔
      LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites q y := by
  rfl

set_option maxHeartbeats 8000000 in




theorem lpReplicaAggregateRankFiveStrictRoute_exists_alternateTarget
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (hzy : LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z y)
    (hdegree :
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card = 2) :
    ∃ y',
      LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z y' ∧
        y' ≠ y ∧
        y' ≠ lpReplicaAggregateDecoratedTargetFlipMultiplicity
          G sites q y := by
  classical
  let C :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z
  obtain ⟨d, hdTarget⟩ := hzy
  have hCtwo : C.card = 2 := hdegree
  obtain ⟨e, heC, hed⟩ := C.exists_mem_ne (by omega) d.1
  let e' : ↑C := ⟨e, heC⟩
  have hed' : e' ≠ d := by
    intro h
    exact hed (congrArg Subtype.val h)
  let y' :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
      G sites hsite q hcard z e'
  refine ⟨y', ⟨e', rfl⟩, ?_, ?_⟩
  · intro hy'y
    apply hed'
    apply
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_injective
        G sites hsite q hcard z
    exact hy'y.trans hdTarget.symm
  · intro hy'flip
    apply hed'
    apply
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_injective
        G sites hsite q hcard z
    calc
      lpReplicaAggregateDecoratedTargetSlotState G sites q
          (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
            G sites hsite q hcard z e') =
          lpReplicaAggregateDecoratedTargetSlotState G sites q
            (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) :=
        congrArg (lpReplicaAggregateDecoratedTargetSlotState G sites q) hy'flip
      _ = lpReplicaAggregateDecoratedTargetSlotState G sites q y := by simp
      _ = lpReplicaAggregateDecoratedTargetSlotState G sites q
          (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
            G sites hsite q hcard z d) :=
        congrArg (lpReplicaAggregateDecoratedTargetSlotState G sites q)
          hdTarget.symm



theorem lpReplicaAggregateDecoratedTarget_card_ge_two
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    2 ≤ Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  let yflip := lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y
  have hne : y ≠ yflip :=
    (lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne G sites q y).symm
  calc
    2 = ({y, yflip} : Finset
        (LPReplicaAggregateDecoratedTarget G sites q)).card :=
      (Finset.card_pair hne).symm
    _ ≤ (Finset.univ : Finset
        (LPReplicaAggregateDecoratedTarget G sites q)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) :=
      Finset.card_univ



theorem lpReplicaAggregateDecoratedTarget_card_ge_three_of_alternate
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y y' : LPReplicaAggregateDecoratedTarget G sites q)
    (hy'y : y' ≠ y)
    (hy'flip : y' ≠
      lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) :
    3 ≤ Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  let yflip := lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y
  have hyflip : y ≠ yflip :=
    (lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne G sites q y).symm
  have hy'mem : y' ∉ ({y, yflip} : Finset
      (LPReplicaAggregateDecoratedTarget G sites q)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hy'y, hy'flip⟩
  calc
    3 = ({y', y, yflip} : Finset
        (LPReplicaAggregateDecoratedTarget G sites q)).card := by
      rw [Finset.card_insert_of_notMem hy'mem, Finset.card_pair hyflip]
    _ ≤ (Finset.univ : Finset
        (LPReplicaAggregateDecoratedTarget G sites q)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) :=
      Finset.card_univ





theorem lpReplicaAggregateRankFiveStrictRoute_one_add_incoming_card_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    1 + (LPReplicaAggregateRankFiveStrictRouteIncoming
        G sites hsite q hcard y).card ≤
      Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  let Incoming := LPReplicaAggregateRankFiveStrictRouteIncoming
    G sites hsite q hcard y
  change 1 + Incoming.card ≤
    Fintype.card (LPReplicaAggregateDecoratedTarget G sites q)
  by_cases hIncoming : Incoming.Nonempty
  · obtain ⟨z, hz⟩ := hIncoming
    have hzy : LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard z y :=
      (mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff
        G sites hsite q hcard y z).mp hz
    obtain ⟨d, hdTarget⟩ := hzy
    have hfiber :=
      LPReplicaAggregateRankFiveStrictRouteIncoming_card_le_candidates
        G sites hsite q hcard y z d hdTarget
    change Incoming.card ≤
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card at hfiber
    rcases
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_eq_one_or_two
          G sites hsite q hcard z with hdegree | hdegree
    · have htarget := lpReplicaAggregateDecoratedTarget_card_ge_two
          G sites q y
      omega
    · obtain ⟨y', _hy'related, hy'y, hy'flip⟩ :=
        lpReplicaAggregateRankFiveStrictRoute_exists_alternateTarget
          G sites hsite q hcard z y ⟨d, hdTarget⟩ hdegree
      have htarget :=
        lpReplicaAggregateDecoratedTarget_card_ge_three_of_alternate
          G sites q y y' hy'y hy'flip
      omega
  · have hzero : Incoming.card = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hIncoming]
      rfl
    have htarget := lpReplicaAggregateDecoratedTarget_card_ge_two G sites q y
    omega




noncomputable def LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    Finset (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  exact insert y
    (insert (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y)
      (Finset.univ.filter fun y' =>
        ∃ z, z ∈ LPReplicaAggregateRankFiveStrictRouteIncoming
            G sites hsite q hcard y ∧
          LPReplicaAggregateRankFiveStrictRouteRelated
            G sites hsite q hcard z y'))



theorem lpReplicaAggregateRankFiveStrictRouteRelated_selectedSeam_eq
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (y y' : LPReplicaAggregateDecoratedTarget G sites q)
    (hzy : LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z y)
    (hzy' : LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z y') :
    y.2.1 = y'.2.1 := by
  obtain ⟨d, rfl⟩ := hzy
  obtain ⟨e, rfl⟩ := hzy'
  simp



theorem lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_selectedSeam
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y y' : LPReplicaAggregateDecoratedTarget G sites q)
    (hy' : y' ∈ LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
      G sites hsite q hcard y) :
    y'.2.1 = y.2.1 := by
  classical
  simp only [LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood,
    Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
  rcases hy' with rfl | hy'flip | ⟨z, hzy, hzy'⟩
  · rfl
  · rw [hy'flip]
    rfl
  · have hzyRelated : LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard z y :=
      (mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff
        G sites hsite q hcard y z).mp hzy
    exact
      lpReplicaAggregateRankFiveStrictRouteRelated_selectedSeam_eq
        G sites hsite q hcard z y' y hzy' hzyRelated



theorem lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_disjoint_of_selectedSeam_ne
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y w : LPReplicaAggregateDecoratedTarget G sites q)
    (hseam : y.2.1 ≠ w.2.1) :
    Disjoint
      (LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
        G sites hsite q hcard y)
      (LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
        G sites hsite q hcard w) := by
  classical
  rw [Finset.disjoint_left]
  intro t hty htw
  apply hseam
  rw [
    ← lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_selectedSeam
      G sites hsite q hcard y t hty,
    ← lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_selectedSeam
      G sites hsite q hcard w t htw]



noncomputable def LPReplicaAggregateRankFiveStrictRouteRerouteGraph
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    SimpleGraph (LPReplicaAggregateDecoratedTarget G sites q) :=
  SimpleGraph.fromRel fun y w =>
    w = lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y ∨
      ∃ z, LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z y ∧
        LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z w




theorem lpReplicaAggregateRankFiveStrictRouteRerouteGraph_adj_selectedSeam_eq
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    {y w : LPReplicaAggregateDecoratedTarget G sites q}
    (hyw : (LPReplicaAggregateRankFiveStrictRouteRerouteGraph
      G sites hsite q hcard).Adj y w) :
    y.2.1 = w.2.1 := by
  classical
  rw [LPReplicaAggregateRankFiveStrictRouteRerouteGraph,
    SimpleGraph.fromRel_adj] at hyw
  rcases hyw.2 with hyw | hwy
  · rcases hyw with hflip | ⟨z, hzy, hzw⟩
    · rw [hflip]
      rfl
    · exact lpReplicaAggregateRankFiveStrictRouteRelated_selectedSeam_eq
        G sites hsite q hcard z y w hzy hzw
  · rcases hwy with hflip | ⟨z, hzw, hzy⟩
    · rw [hflip]
      rfl
    · exact (lpReplicaAggregateRankFiveStrictRouteRelated_selectedSeam_eq
        G sites hsite q hcard z w y hzw hzy).symm



theorem lpReplicaAggregateRankFiveStrictRouteRerouteGraph_reachable_selectedSeam_eq
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    {y w : LPReplicaAggregateDecoratedTarget G sites q}
    (hyw : (LPReplicaAggregateRankFiveStrictRouteRerouteGraph
      G sites hsite q hcard).Reachable y w) :
    y.2.1 = w.2.1 := by
  have hreach := (SimpleGraph.reachable_iff_reflTransGen y w).mp hyw
  exact Relation.ReflTransGen.trans_induction_on hreach
    (fun _ => rfl)
    (fun hadj =>
      lpReplicaAggregateRankFiveStrictRouteRerouteGraph_adj_selectedSeam_eq
        G sites hsite q hcard hadj)
    (fun _ _ hleft hright => Eq.trans hleft hright)


noncomputable def LPReplicaAggregateRankFiveStrictRouteRerouteComponent
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    Finset (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  exact Finset.univ.filter fun w =>
    (LPReplicaAggregateRankFiveStrictRouteRerouteGraph
      G sites hsite q hcard).Reachable y w



theorem lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_subset_component
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
        G sites hsite q hcard y ⊆
      LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y := by
  classical
  intro w hw
  rw [LPReplicaAggregateRankFiveStrictRouteRerouteComponent,
    Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  simp only [LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood,
    Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  rcases hw with rfl | hwflip | ⟨z, hzin, hzw⟩
  · exact SimpleGraph.Reachable.refl _
  · rw [hwflip]
    apply SimpleGraph.Adj.reachable
    rw [LPReplicaAggregateRankFiveStrictRouteRerouteGraph,
      SimpleGraph.fromRel_adj]
    refine ⟨lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne
      G sites q y |>.symm, Or.inl ?_⟩
    exact Or.inl rfl
  · have hzy : LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard z y :=
      (mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff
        G sites hsite q hcard y z).mp hzin
    by_cases hyw : y = w
    · subst w
      exact SimpleGraph.Reachable.refl _
    · apply SimpleGraph.Adj.reachable
      rw [LPReplicaAggregateRankFiveStrictRouteRerouteGraph,
        SimpleGraph.fromRel_adj]
      exact ⟨hyw, Or.inl (Or.inr ⟨z, hzy, hzw⟩)⟩


theorem lpReplicaAggregateRankFiveStrictRouteRerouteComponent_eq_of_reachable
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y w : LPReplicaAggregateDecoratedTarget G sites q)
    (hyw : (LPReplicaAggregateRankFiveStrictRouteRerouteGraph
      G sites hsite q hcard).Reachable y w) :
    LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y =
      LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard w := by
  classical
  ext t
  simp only [LPReplicaAggregateRankFiveStrictRouteRerouteComponent,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun hyt => hyw.symm.trans hyt
  · exact fun hwt => hyw.trans hwt


theorem lpReplicaAggregateRankFiveStrictRouteRerouteComponent_disjoint_of_not_reachable
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y w : LPReplicaAggregateDecoratedTarget G sites q)
    (hyw : ¬ (LPReplicaAggregateRankFiveStrictRouteRerouteGraph
      G sites hsite q hcard).Reachable y w) :
    Disjoint
      (LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y)
      (LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard w) := by
  classical
  rw [Finset.disjoint_left]
  intro t hyt hwt
  rw [LPReplicaAggregateRankFiveStrictRouteRerouteComponent,
    Finset.mem_filter] at hyt hwt
  exact hyw (hyt.2.trans hwt.2.symm)




theorem
    lpReplicaAggregateRankFiveStrictRouteRerouteComponent_disjoint_of_selectedSeam_ne
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y w : LPReplicaAggregateDecoratedTarget G sites q)
    (hseam : y.2.1 ≠ w.2.1) :
    Disjoint
      (LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y)
      (LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard w) := by
  apply lpReplicaAggregateRankFiveStrictRouteRerouteComponent_disjoint_of_not_reachable
    G sites hsite q hcard y w
  intro hyw
  exact hseam
    (lpReplicaAggregateRankFiveStrictRouteRerouteGraph_reachable_selectedSeam_eq
      G sites hsite q hcard hyw)


theorem lpReplicaAggregateRankFiveStrictRouteRerouteComponent_flip_mem
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y t : LPReplicaAggregateDecoratedTarget G sites q)
    (ht : t ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent
      G sites hsite q hcard y) :
    lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q t ∈
      LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y := by
  classical
  rw [LPReplicaAggregateRankFiveStrictRouteRerouteComponent,
    Finset.mem_filter] at ht ⊢
  refine ⟨Finset.mem_univ _, ht.2.trans ?_⟩
  apply SimpleGraph.Adj.reachable
  rw [LPReplicaAggregateRankFiveStrictRouteRerouteGraph,
    SimpleGraph.fromRel_adj]
  refine ⟨lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne
      G sites q t |>.symm, Or.inl ?_⟩
  exact Or.inl rfl



theorem lpReplicaAggregateRankFiveStrictRouteRerouteComponent_related_mem
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y t w : LPReplicaAggregateDecoratedTarget G sites q)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (ht : t ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent
      G sites hsite q hcard y)
    (hzt : LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z t)
    (hzw : LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z w) :
    w ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent
      G sites hsite q hcard y := by
  classical
  rw [LPReplicaAggregateRankFiveStrictRouteRerouteComponent,
    Finset.mem_filter] at ht ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  by_cases htw : t = w
  · subst w
    exact ht.2
  · apply ht.2.trans
    apply SimpleGraph.Adj.reachable
    rw [LPReplicaAggregateRankFiveStrictRouteRerouteGraph,
      SimpleGraph.fromRel_adj]
    exact ⟨htw, Or.inl (Or.inr ⟨z, hzt, hzw⟩)⟩


noncomputable def LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    Finset (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) := by
  classical
  exact Finset.univ.filter fun z =>
    ∃ t, t ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y ∧
      LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard z t



theorem lpReplicaAggregateRankFiveStrictRouteRerouteComponentSources_card_le
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    (LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources
        G sites hsite q hcard y).card ≤
      (LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y).card := by
  classical
  let S := LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources
    G sites hsite q hcard y
  let C := LPReplicaAggregateRankFiveStrictRouteRerouteComponent
    G sites hsite q hcard y
  let N := Finset.univ.filter fun target :
      LPReplicaAggregateDecoratedTarget G sites q =>
    ∃ source ∈ S, LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard source target
  have hHall : S.card ≤ N.card := by
    exact LPReplicaAggregateRankFiveStrictRouteHall
      G sites hsite q hcard S
  apply hHall.trans
  apply Finset.card_le_card
  intro t ht
  simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  obtain ⟨z, hzS, hzt⟩ := ht
  have hzData : ∃ w, w ∈ C ∧
      LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard z w := by
    simpa only [S, C,
      LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources,
      Finset.mem_filter, Finset.mem_univ, true_and] using hzS
  obtain ⟨w, hwC, hzw⟩ := hzData
  exact lpReplicaAggregateRankFiveStrictRouteRerouteComponent_related_mem
    G sites hsite q hcard y w t z hwC hzw hzt




theorem
    lpReplicaAggregateRankFiveStrictRoute_one_add_componentSources_card_le_of_targetLoad_lt_one
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y t : LPReplicaAggregateDecoratedTarget G sites q)
    (ht : t ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent
      G sites hsite q hcard y)
    (hslack :
      (∑ z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight
          G sites hsite q hcard z t) < 1) :
    1 + (LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources
        G sites hsite q hcard y).card ≤
      (LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y).card := by
  classical
  let S := LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources
    G sites hsite q hcard y
  let C := LPReplicaAggregateRankFiveStrictRouteRerouteComponent
    G sites hsite q hcard y
  let W := LPReplicaAggregateRankFiveStrictRouteWeight
    G sites hsite q hcard
  have hsourceMass (z) (hz : z ∈ S) :
      (∑ target ∈ C, W z target) = 1 := by
    rw [← LPReplicaAggregateRankFiveStrictRouteWeight_sum_target
      G sites hsite q hcard z]
    apply Finset.sum_subset (Finset.subset_univ C)
    intro target _ htarget
    apply LPReplicaAggregateRankFiveStrictRouteWeight_eq_zero_of_not_related
    intro hzt
    have hzData : ∃ w, w ∈ C ∧
        LPReplicaAggregateRankFiveStrictRouteRelated
          G sites hsite q hcard z w := by
      simpa only [S, C,
        LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources,
        Finset.mem_filter, Finset.mem_univ, true_and] using hz
    obtain ⟨w, hw, hzw⟩ := hzData
    exact htarget
      (lpReplicaAggregateRankFiveStrictRouteRerouteComponent_related_mem
        G sites hsite q hcard y w target z hw hzw hzt)
  have htargetMass (target) (htarget : target ∈ C) :
      (∑ z ∈ S, W z target) ≤ 1 := by
    calc
      (∑ z ∈ S, W z target) ≤ ∑ z, W z target := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ S)
          (fun z _ _ =>
            LPReplicaAggregateRankFiveStrictRouteWeight_nonneg
              G sites hsite q hcard z target)
      _ ≤ 1 := lpReplicaAggregateRankFiveStrictRouteTargetLoad
        G sites hsite q hcard target
  have hrestrictedSlack : (∑ z ∈ S, W z t) < 1 := by
    apply lt_of_le_of_lt _ hslack
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ S)
      (fun z _ _ =>
        LPReplicaAggregateRankFiveStrictRouteWeight_nonneg
          G sites hsite q hcard z t)
  have hlt : S.card < C.card :=
    finiteSubset_card_lt_of_fractionalWeights_of_target_slack
      W S C hsourceMass htargetMass t ht hrestrictedSlack
  change 1 + S.card ≤ C.card
  omega




noncomputable def
    lpReplicaAggregateRankFiveStrictRouteComponentAllocation_of_targetLoad_lt_one
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y t : LPReplicaAggregateDecoratedTarget G sites q)
    (ht : t ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent
      G sites hsite q hcard y)
    (hslack :
      (∑ z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q,
        LPReplicaAggregateRankFiveStrictRouteWeight
          G sites hsite q hcard z t) < 1) :
    Unit ⊕ ↑(LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources
        G sites hsite q hcard y) ↪
      ↑(LPReplicaAggregateRankFiveStrictRouteRerouteComponent
        G sites hsite q hcard y) := by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_coe] using
    lpReplicaAggregateRankFiveStrictRoute_one_add_componentSources_card_le_of_targetLoad_lt_one
      G sites hsite q hcard y t ht hslack

theorem lpReplicaAggregateRankFiveStrictRoute_pair_subset_rerouteNeighborhood
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y y' : LPReplicaAggregateDecoratedTarget G sites q)
    (hy' : y' = y ∨ y' =
      lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) :
    y' ∈ LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
      G sites hsite q hcard y := by
  rcases hy' with rfl | rfl <;>
    simp [LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood]



theorem
    lpReplicaAggregateRankFiveStrictRoute_one_add_incoming_card_le_rerouteNeighborhood
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    1 + (LPReplicaAggregateRankFiveStrictRouteIncoming
        G sites hsite q hcard y).card ≤
      (LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
        G sites hsite q hcard y).card := by
  classical
  let Incoming := LPReplicaAggregateRankFiveStrictRouteIncoming
    G sites hsite q hcard y
  let N := LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
    G sites hsite q hcard y
  change 1 + Incoming.card ≤ N.card
  have hpair : 2 ≤ N.card := by
    let yflip := lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y
    have hne : y ≠ yflip :=
      (lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne G sites q y).symm
    calc
      2 = ({y, yflip} : Finset
          (LPReplicaAggregateDecoratedTarget G sites q)).card :=
        (Finset.card_pair hne).symm
      _ ≤ N.card := Finset.card_le_card
        (by
          intro y' hy'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
          exact
            lpReplicaAggregateRankFiveStrictRoute_pair_subset_rerouteNeighborhood
              G sites hsite q hcard y y' hy')
  by_cases hIncoming : Incoming.Nonempty
  · obtain ⟨z, hz⟩ := hIncoming
    have hzy : LPReplicaAggregateRankFiveStrictRouteRelated
        G sites hsite q hcard z y :=
      (mem_LPReplicaAggregateRankFiveStrictRouteIncoming_iff
        G sites hsite q hcard y z).mp hz
    obtain ⟨d, hdTarget⟩ := hzy
    have hfiber :=
      LPReplicaAggregateRankFiveStrictRouteIncoming_card_le_candidates
        G sites hsite q hcard y z d hdTarget
    change Incoming.card ≤
      (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
        G sites hsite q z).card at hfiber
    rcases
        lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_eq_one_or_two
          G sites hsite q hcard z with hdegree | hdegree
    · omega
    · obtain ⟨y', hy'related, hy'y, hy'flip⟩ :=
        lpReplicaAggregateRankFiveStrictRoute_exists_alternateTarget
          G sites hsite q hcard z y ⟨d, hdTarget⟩ hdegree
      have hy'mem : y' ∈ N := by
        change y' ∈ LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
          G sites hsite q hcard y
        simp only [LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood,
          Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr (Or.inr ⟨z, hz, hy'related⟩)
      have hthree : 3 ≤ N.card := by
        let yflip :=
          lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y
        have hyflip : y ≠ yflip :=
          (lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne
            G sites q y).symm
        have hy'pair : y' ∉ ({y, yflip} : Finset
            (LPReplicaAggregateDecoratedTarget G sites q)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hy'y, hy'flip⟩
        calc
          3 = ({y', y, yflip} : Finset
              (LPReplicaAggregateDecoratedTarget G sites q)).card := by
            rw [Finset.card_insert_of_notMem hy'pair,
              Finset.card_pair hyflip]
          _ ≤ N.card := Finset.card_le_card (by
            intro t ht
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with ht | ht | ht
            · rw [ht]
              exact hy'mem
            · exact
                (lpReplicaAggregateRankFiveStrictRoute_pair_subset_rerouteNeighborhood
                  G sites hsite q hcard y t) (Or.inl ht)
            · exact
                (lpReplicaAggregateRankFiveStrictRoute_pair_subset_rerouteNeighborhood
                  G sites hsite q hcard y t) (Or.inr ht))
      omega
  · have hzero : Incoming.card = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hIncoming]
      rfl
    omega



noncomputable def lpReplicaAggregateRankFiveStrictRouteTargetLocalAllocation
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    (Unit ⊕ ↑(LPReplicaAggregateRankFiveStrictRouteIncoming
        G sites hsite q hcard y)) ↪
      ↑(LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood
        G sites hsite q hcard y) := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_coe] using
    lpReplicaAggregateRankFiveStrictRoute_one_add_incoming_card_le_rerouteNeighborhood
      G sites hsite q hcard y

set_option maxHeartbeats 1200000 in



theorem lpReplicaLowRowMarkedOutputData_not_hasStrictPhysicalDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z)
    (d : LPReplicaLowRowMarkedOutputData G sites q z) :
    ¬ LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites i j q d.output := by
  classical
  rcases d.branch with ⟨y, hy, hc⟩ | ⟨y, hy, hc⟩
  · obtain ⟨s, hp, _hL, _hP, hmove, y', _hyBal, hyState, hyPres⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_iSeam
        G sites hsite hij q hcard z hlow.1 d.copy d.copy_active hc
    have hout : d.output = Sum.inl y' := by
      rw [hy]
      apply lpReplicaOffdiagDecoratedTargetBranchedSlotState_injective
        G sites i j q
      apply Prod.ext
      · rfl
      · have hdState := d.state_eq
        rw [hy] at hdState
        exact hdState.trans hyState.symm
    rw [hout, LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence,
      hyPres]
    rw [
      lpReplicaDecoratedOrbitAtomOfBalancedSelector_left_hasStrictPhysicalDoubleIncidence]
    rcases s with ⟨sp, sorbit, stag, sgate, slabel, sselector,
      sfalse, strue, srow0, srow1⟩
    dsimp at hp hmove ⊢
    subst sp
    rw [eq_of_heq hmove]
    exact lpReplicaOffdiagDecoratedSource_rankFive_low_singletonToggle_not_strictRaw
      G sites hsite hij q hcard z hlow d.copy d.copy_active
  · obtain ⟨s, hp, _hL, _hP, hmove, y', _hyBal, hyState,
      s', hyPres, hp', hselector', htag'⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_jSeam
        G sites hsite hij q hcard z hlow.1 d.copy d.copy_active hc
    have hout : d.output = Sum.inr y' := by
      rw [hy]
      apply lpReplicaOffdiagDecoratedTargetBranchedSlotState_injective
        G sites i j q
      apply Prod.ext
      · rfl
      · have hdState := d.state_eq
        rw [hy] at hdState
        exact hdState.trans hyState.symm
    rw [hout, LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence,
      hyPres]
    rw [
      lpReplicaDecoratedOrbitAtomOfBalancedSelector_left_hasStrictPhysicalDoubleIncidence]
    rcases s with ⟨sp, sorbit, stag, sgate, slabel, sselector,
      sfalse, strue, srow0, srow1⟩
    rcases s' with ⟨sp', sorbit', stag', sgate', slabel', sselector',
      sfalse', strue', srow0', srow1'⟩
    dsimp at hp hp' hselector' htag' hmove ⊢
    subst sp
    subst sp'
    rw [eq_of_heq hselector', eq_of_heq htag', eq_of_heq hmove]
    exact lpReplicaOffdiagDecoratedSource_rankFive_low_singletonToggle_not_strictRaw
      G sites hsite hij q hcard z hlow d.copy d.copy_active

end

end StatMech.Ising
