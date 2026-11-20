/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateBound












open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveAggregateHighRowDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

local instance lpReplicaRankFiveAggregateHighRowFintypeState
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaOrbitFourColorSlotState G sites q) := by
  classical
  let encode := fun s : LPReplicaOrbitFourColorSlotState G sites q =>
    (s.allocation, s.color)
  exact Fintype.ofInjective encode (by
    intro s t h
    exact LPReplicaOrbitFourColorSlotState.ext
      (congrArg Prod.fst h) (congrArg Prod.snd h))

set_option maxHeartbeats 1000000 in




theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_jSeam
    (G : SimpleGraph V) (sites : I -> V) {i j : I}
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsat : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites j) :
    ∃ y : LPReplicaDecoratedOrbitAtom G sites
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q,
      LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inr y) ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
            (Sum.inr y)).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
              z.1.1.2 z.2.2 {c})
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let m := z.1.1.1
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let d0 := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  let P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) := Finset.univ \ {c}
  have hall (a) : d0.1 a = (true, false) := by
    have ha : a ∈ lpReplicaCurrentCopies G sites m d0.1 true false := by
      rw [hsat]
      exact Finset.mem_univ a
    simpa only [lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using ha
  have hctag0 : d0.1 c = (true, false) := hall c
  have hcurrent : (d.1 c).2 = false := by
    change (lpReplicaSwapRowsTag d0.1 c).2 = false
    simp only [lpReplicaSwapRowsTag, hctag0]
  have hcurr := lpReplicaRowGate_compl_singleton_currentSources
    G sites m B d.1 d.2 c hcurrent
  have hcends : E c = s(lpReplicaCurrentLeft sites j,
      lpReplicaCurrentRight sites j) := by
    simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hc
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Sj := by
    simpa only [Sj, lpMatchingSeamSource] using
      randomCurrent_sources_singleton_of_ends_eq E c (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends
  have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = false) = Si ∆ T := by
    calc
      _ = B ∆ StatMech.Sharpness.RandomCurrent.sources E {c} := by
        simpa only [P, E] using hcurr.1
      _ = B ∆ Sj := by rw [hsingle]
      _ = Si ∆ T := by
        change (Si ∆ Sj ∆ T) ∆ Sj = Si ∆ T
        rw [symmDiff_comm Si Sj, symmDiff_assoc Sj Si T,
          symmDiff_symmDiff_self']
  have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = true) = ∅ := by
    simpa only [P, E, B] using hcurr.2
  have hmove : lpReplicaToggleRows G sites m P d.1 =
      lpReplicaToggleRows G sites m {c} d0.1 := by
    simpa only [P, d, d0,
      lpReplicaDecoratedSourceSwappedRowGateData] using
        lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag
          G sites m d0.1 c
  have hrow1Sub : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) true ⊆
        lpReplicaRowCopies G sites m d0.1 true := by
    rw [hmove]
    intro a ha
    simp only [lpReplicaRowCopies, lpReplicaToggleRows, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha ⊢
    exact congrArg Prod.fst (hall a)
  have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    exact d0.2.2.2.2.2.2
      (StatMech.GrahamGHS.FourColor.connK_mono hrow1Sub hconn)
  have hrow0Sub : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) false ⊆ {c} := by
    rw [hmove]
    intro a ha
    simp only [lpReplicaRowCopies, lpReplicaToggleRows, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton] at ha ⊢
    by_contra hac
    simp only [hac] at ha
    exact Bool.false_ne_true (ha.symm.trans (congrArg Prod.fst (hall a)))
  have hsingleDisconn : ¬ StatMech.Sharpness.RandomCurrent.connK E {c}
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    have hghost : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ≠
        lpReplicaCurrentGhost1 := by
      simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]
    obtain ⟨a, ha, hg0⟩ := exists_mem_ends_of_connK_of_ne E
      {c} hghost hconn
    have hac : a = c := by simpa only [Finset.mem_singleton] using ha
    subst a
    change (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ c.1.1 at hg0
    rw [hc] at hg0
    simp [lpReplicaCurrentSeamEdge, lpReplicaCurrentLeft,
      lpReplicaCurrentRight, lpReplicaCurrentGhost0] at hg0
  have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    exact hsingleDisconn
      (StatMech.GrahamGHS.FourColor.connK_mono hrow0Sub hconn)
  let s : LPReplicaBalancedSelector G sites B (Si ∆ T) q := {
    profile := m
    orbit := z.1.1.2
    tag := d.1
    gate := d.2
    orbitLabel := z.2.2
    selector := P
    falseSource := hfalseSource
    trueSource := htrueSource
    row0Disconn := hrow0Disconn
    row1Disconn := hrow1Disconn }
  let sourceTag := lpReplicaOrientedFourColorTag G sites ∅ B q
    (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z)
  have hsourceTag : sourceTag = d0.1 :=
    lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  have hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
    lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites j m c hc
  let s' : LPReplicaBalancedSelector G sites (Sj ∆ Si ∆ T) (Si ∆ T) q := {
    profile := s.profile
    orbit := s.orbit
    tag := s.tag
    gate := by
      rw [symmDiff_comm Sj Si]
      exact s.gate
    orbitLabel := s.orbitLabel
    selector := s.selector
    falseSource := s.falseSource
    trueSource := s.trueSource
    row0Disconn := s.row0Disconn
    row1Disconn := s.row1Disconn }
  have hgeneric := lpReplicaBalancedSelector_slotState_of_singletonToggle
    G sites Sj Si T q s' c sourceTag (by
      rw [hsourceTag]
      exact hmove) hfixed
  have hfixedD : (Si ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Si ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites i
  let y := lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
    G sites j i q s'
  refine ⟨y, Or.inr ⟨s', rfl⟩, ?_⟩
  change (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites j i q
    (Sum.inl y)).2 = _
  unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
  unfold y lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
  dsimp only
  rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Sj
    ((Si ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Si ∆ T) q hfixedD]
  exact hgeneric



def LPReplicaOffdiagDecoratedSource.IsResolvableHighRowRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) : Prop :=
  LPReplicaOffdiagDecoratedSource.IsHighRowRankFive G sites i j q z /\
    (LPReplicaOffdiagDecoratedSource.IsSaturatedRankFive G sites i j q z ->
      (exists c : StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1,
          c.1.1 = lpReplicaCurrentSeamEdge sites i) ∨
        (exists c : StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1,
          c.1.1 = lpReplicaCurrentSeamEdge sites j))



theorem lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_nonempty_of_resolvableHighRow
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hresolve : LPReplicaOffdiagDecoratedSource.IsResolvableHighRowRankFive
      G sites i j q z) :
    (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
      (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).Nonempty := by
  classical
  rcases hresolve.1 with hsat | hthree
  · rcases hresolve.2 hsat with ⟨c, hc⟩ | ⟨c, hc⟩
    · obtain ⟨y, hyBal, hyTrace, _⟩ :=
        lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_mask_four_of_iSeam
          G sites hsite hij q hcard z hsat c hc
      refine ⟨y, ?_⟩
      simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
        lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨hyBal, hyTrace⟩
    · obtain ⟨y, hyBal, hstate⟩ :=
        lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_jSeam
          G sites q z hsat c hc
      refine ⟨Sum.inr y, ?_⟩
      simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
        lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨hyBal, ?_⟩
      unfold lpReplicaOffdiagDecoratedTargetCrossTrace
        lpReplicaOffdiagDecoratedSourceCrossTrace
      rw [hstate]
      exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
        G sites q _ _
  · exact
      lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_nonempty_of_active_card_eq_three
        G sites hsite hij q hcard z hthree.1


noncomputable def lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
    G sites i j q u).filter
      (LPReplicaOffdiagDecoratedSource.IsResolvableHighRowRankFive
        G sites i j q)



theorem lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_one
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
      G sites i j q u).card <= 1 := by
  classical
  calc
    (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
        G sites i j q u).card <=
      (lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive
        G sites i j q u).card := by
      apply Finset.card_le_card
      intro z hz
      simp only [lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive,
        lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive,
        Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hz.2.1⟩
    _ <= 1 :=
      lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive_card_le_one
        G sites hsite hij q hcard u



theorem lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
      G sites i j q u).card <=
      (lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u).card := by
  classical
  have hsource :=
    lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_one
      G sites hsite hij q hcard u
  by_cases hempty :
      (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
        G sites i j q u).Nonempty
  · obtain ⟨z, hz⟩ := hempty
    have hz' := Finset.mem_filter.mp hz
    have htarget :=
      lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_nonempty_of_resolvableHighRow
        G sites hsite hij q hcard z hz'.2
    have htrace := (Finset.mem_filter.mp hz'.1).2
    rw [htrace] at htarget
    exact Nat.le_trans hsource (Finset.card_pos.mpr htarget)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.card_empty]
    exact Nat.zero_le _




noncomputable def lpReplicaOffdiagDecoratedTargetToAggregate
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOffdiagDecoratedTarget G sites i j q ->
      LPReplicaAggregateDecoratedTarget G sites q
  | Sum.inl y => ⟨0, ⟨i, ⟨j, y⟩⟩⟩
  | Sum.inr y => ⟨1, ⟨j, ⟨i, y⟩⟩⟩


theorem lpReplicaOffdiagDecoratedTargetToAggregate_crossTrace
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    lpReplicaAggregateDecoratedTargetCrossTrace G sites q
        (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q y) =
      lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y := by
  cases y <;> rfl


noncomputable def lpReplicaOffdiagResolvableHighRowSourcesRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact Finset.univ.filter
    (LPReplicaOffdiagDecoratedSource.IsResolvableHighRowRankFive
      G sites i j q)



theorem lpReplicaOffdiagResolvableHighRowSourcesRankFive_card_eq_sum_traceFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagResolvableHighRowSourcesRankFive
      G sites i j q).card =
      ∑ u : LPReplicaOrbitFourColorSlotState G sites q,
        (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
          G sites i j q u).card := by
  classical
  let trace := lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q
  simpa only [lpReplicaOffdiagResolvableHighRowSourcesRankFive,
    lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive, trace,
    lpReplicaOffdiagDecoratedSourceCrossTraceFiber,
    Finset.filter_filter, and_comm, and_left_comm, and_assoc] using
      Finset.card_eq_sum_card_fiberwise
        (s := lpReplicaOffdiagResolvableHighRowSourcesRankFive
          G sites i j q)
        (t := (Finset.univ : Finset
          (LPReplicaOrbitFourColorSlotState G sites q)))
        (f := trace) (fun _ _ => Finset.mem_univ _)



theorem lpReplicaOffdiagResolvableHighRowSourcesRankFive_card_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    (lpReplicaOffdiagResolvableHighRowSourcesRankFive
      G sites i j q).card <=
      Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  rw [lpReplicaOffdiagResolvableHighRowSourcesRankFive_card_eq_sum_traceFibers]
  calc
    (∑ u : LPReplicaOrbitFourColorSlotState G sites q,
        (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
          G sites i j q u).card) <=
      ∑ u : LPReplicaOrbitFourColorSlotState G sites q,
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q u).card := by
      exact Finset.sum_le_sum fun u _ =>
        lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_target
          G sites hsite hij q hcard u
    _ = (lpReplicaOffdiagBalancedOutputs G sites i j q).card := by
      symm
      simpa using
        (lpReplicaOffdiagBalancedOutputs_card_eq_sum_crossTraceFibers
          G sites i j q
          (Finset.univ : Finset
            (LPReplicaOrbitFourColorSlotState G sites q))
          (fun _ _ => Finset.mem_univ _))
    _ <= Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)



def LPReplicaAggregateResolvableHighRowSourceRankFive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Sigma fun i : I => Sigma fun j : I =>
    Fin (if i = j then 0 else 1) ×
      ↑(lpReplicaOffdiagResolvableHighRowSourcesRankFive G sites i j q)

noncomputable instance instFintypeLPReplicaAggregateResolvableHighRowSourceRankFive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaAggregateResolvableHighRowSourceRankFive G sites q) := by
  unfold LPReplicaAggregateResolvableHighRowSourceRankFive
  infer_instance


theorem card_lpReplicaAggregateResolvableHighRowSourceRankFive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card
        (LPReplicaAggregateResolvableHighRowSourceRankFive G sites q) =
      ∑ i : I, ∑ j : I, if i = j then 0 else
        (lpReplicaOffdiagResolvableHighRowSourcesRankFive
          G sites i j q).card := by
  classical
  unfold LPReplicaAggregateResolvableHighRowSourceRankFive
  change Fintype.card
      (Sigma fun i : I => Sigma fun j : I =>
        Fin (if i = j then 0 else 1) ×
          ↑(lpReplicaOffdiagResolvableHighRowSourcesRankFive
            G sites i j q)) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.card_prod, Fintype.card_coe]
  by_cases hij : i = j <;>
    simp [hij, lpReplicaOffdiagResolvableHighRowSourcesRankFive]



theorem sum_card_lpReplicaOffdiagDecoratedTarget_eq_aggregate
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (∑ i : I, ∑ j : I,
      Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q)) =
      Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  rw [card_lpReplicaAggregateDecoratedTarget]
  simp only [LPReplicaOffdiagDecoratedTarget, Fintype.card_sum]
  let a : I -> I -> Nat := fun i j => Fintype.card
    (LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q)
  change (∑ i : I, ∑ j : I, (a i j + a j i)) =
    ∑ i : I, ∑ j : I, 2 * a i j
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  omega





noncomputable def lpReplicaAggregateResolvableHighRowRankFiveEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    LPReplicaAggregateResolvableHighRowSourceRankFive G sites q ↪
      LPReplicaAggregateDecoratedTarget G sites q := by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  rw [card_lpReplicaAggregateResolvableHighRowSourceRankFive,
    ← sum_card_lpReplicaOffdiagDecoratedTarget_eq_aggregate]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · rw [if_neg hij]
    exact lpReplicaOffdiagResolvableHighRowSourcesRankFive_card_le_target
      G sites hsite hij q hcard

end

end StatMech.Ising
