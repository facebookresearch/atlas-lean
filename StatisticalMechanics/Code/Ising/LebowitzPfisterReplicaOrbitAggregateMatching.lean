/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber
import Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching
import Code.Ising.LebowitzPfisterReplicaOffdiagSwitching
import Code.Foundations.EqualFiberHall











open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaAggregateMatchingDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



theorem lpReplicaAggregateDecoratedSource_indices_ne
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    z.1 ≠ z.2.1 := by
  rcases z with ⟨i, j, w, atom⟩
  dsimp only
  intro hij
  subst j
  have w0 : Fin 0 := by simpa using w
  exact Fin.elim0 w0



noncomputable def lpReplicaAggregateDecoratedSourceSelectedSeam
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) : I :=
  lpReplicaOffdiagSeamSelector G sites hsite z.1 z.2.1
    (lpReplicaAggregateDecoratedSource_indices_ne G sites q z)
    (StatMech.Sharpness.ofEdgeFun
      (lpReplicaCurrentGraph G sites) z.2.2.2.1.1.1)

set_option maxHeartbeats 800000 in



theorem lpReplicaAggregateDecoratedSourceSelectedSeam_connected
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    StatMech.Sharpness.CurrentConnected (lpReplicaCurrentGraph G sites)
      (StatMech.Sharpness.ofEdgeFun
        (lpReplicaCurrentGraph G sites) z.2.2.2.1.1.1)
      (lpReplicaCurrentLeft sites
        (lpReplicaAggregateDecoratedSourceSelectedSeam
          G sites hsite q z))
      (lpReplicaCurrentRight sites
        (lpReplicaAggregateDecoratedSourceSelectedSeam
          G sites hsite q z)) := by
  let i := z.1
  let j := z.2.1
  let atom := z.2.2.2
  let m := atom.1.1.1
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q atom
  let B := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
    lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
  have hfull : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m) Finset.univ = B := by
    have h := lpReplicaRowGate_fullSources G sites m ∅ B d.1 d.2
    calc
      _ = ∅ ∆ B := h
      _ = B := by
        ext x
        simp [Finset.mem_symmDiff]
  have hsources := StatMech.Sharpness.FluxEdgeCopy.sources_eq
    (G := lpReplicaCurrentGraph G sites) m
      (Finset.univ : Finset
        (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m))
  rw [StatMech.Sharpness.FluxEdgeCopy.profileFlux_univ] at hsources
  have hsrc : StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites)
      (StatMech.Sharpness.ofEdgeFun
        (lpReplicaCurrentGraph G sites) m) = B :=
    hsources.symm.trans hfull
  have hconn := lpReplicaOffdiagSeamSelector_connected G sites hsite
    (lpReplicaAggregateDecoratedSource_indices_ne G sites q z) m hsrc
  simpa only [i, j, atom, m, B,
    lpReplicaAggregateDecoratedSourceSelectedSeam] using hconn

set_option maxHeartbeats 800000 in



theorem lpReplicaAggregateDecoratedSourceSelectedSeam_positive
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    0 < StatMech.Sharpness.ofEdgeFun
        (lpReplicaCurrentGraph G sites) z.2.2.2.1.1.1
      (lpReplicaCurrentSeamEdge sites
        (lpReplicaAggregateDecoratedSourceSelectedSeam
          G sites hsite q z)) := by
  let i := z.1
  let j := z.2.1
  let atom := z.2.2.2
  let m := atom.1.1.1
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q atom
  let B := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
    lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
  have hfull : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m) Finset.univ = B := by
    have h := lpReplicaRowGate_fullSources G sites m ∅ B d.1 d.2
    calc
      _ = ∅ ∆ B := h
      _ = B := by
        ext x
        simp [Finset.mem_symmDiff]
  have hsources := StatMech.Sharpness.FluxEdgeCopy.sources_eq
    (G := lpReplicaCurrentGraph G sites) m
      (Finset.univ : Finset
        (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m))
  rw [StatMech.Sharpness.FluxEdgeCopy.profileFlux_univ] at hsources
  have hsrc : StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites)
      (StatMech.Sharpness.ofEdgeFun
        (lpReplicaCurrentGraph G sites) m) = B :=
    hsources.symm.trans hfull
  have hpos := lpReplicaOffdiagSeamSelector_positive G sites hsite
    (lpReplicaAggregateDecoratedSource_indices_ne G sites q z) m hsrc
  simpa only [i, j, atom, m, B,
    lpReplicaAggregateDecoratedSourceSelectedSeam] using hpos



theorem lpReplicaAggregateDecoratedSourceSelectedSeam_exists_copy
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.2.2.2.1.1.1,
      c.1.1 = lpReplicaCurrentSeamEdge sites
        (lpReplicaAggregateDecoratedSourceSelectedSeam
          G sites hsite q z) := by
  let H := lpReplicaCurrentGraph G sites
  let m := z.2.2.2.1.1.1
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q z
  have hmem : lpReplicaCurrentSeamEdge sites k ∈ H.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]
    unfold lpReplicaCurrentSeamEdge
    rw [SimpleGraph.mem_edgeSet]
    unfold lpReplicaCurrentLeft lpReplicaCurrentRight
    rw [lpReplicaCurrentGraph_adj_left_right_iff]
    exact ⟨k, rfl, rfl⟩
  let e : H.edgeFinset := ⟨lpReplicaCurrentSeamEdge sites k, hmem⟩
  have hpos := lpReplicaAggregateDecoratedSourceSelectedSeam_positive
    G sites hsite q z
  have hpos' : 0 < m e := by
    unfold StatMech.Sharpness.ofEdgeFun at hpos
    rw [dif_pos hmem] at hpos
    simpa only [H, m, k, e] using hpos
  exact ⟨⟨e, ⟨0, hpos'⟩⟩, rfl⟩



abbrev LPReplicaAggregatePooledIntermediate
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Sigma fun i : I => LPReplicaDecoratedOrbitAtom G sites
    (lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) ∅ q



noncomputable def lpReplicaAggregatePooledSourceIntermediate
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    LPReplicaAggregatePooledIntermediate G sites q := by
  let hij := lpReplicaAggregateDecoratedSource_indices_ne G sites q z
  cases lpReplicaOffdiagPooledSourceIntermediate
      G sites hsite hij q z.2.2.2 with
  | inl u => exact ⟨z.1, u⟩
  | inr u => exact ⟨z.2.1, u⟩



noncomputable def lpReplicaAggregatePooledTargetIntermediate
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    LPReplicaAggregatePooledIntermediate G sites q :=
  ⟨y.2.1, lpReplicaOffdiagPooledTargetLeftIntermediate
    G sites y.2.1 y.2.2.1 q y.2.2.2⟩



def LPReplicaAggregatePooledRelated
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q) : Prop :=
  lpReplicaAggregatePooledTargetIntermediate G sites q y =
    lpReplicaAggregatePooledSourceIntermediate G sites hsite q z


noncomputable def lpReplicaAggregatePooledNeighbors
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    Finset (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  exact Finset.univ.filter fun y =>
    LPReplicaAggregatePooledRelated G sites hsite q z y


noncomputable def LPReplicaAggregatePooledHall
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop := by
  classical
  exact forall S : Finset (LPReplicaAggregateDecoratedSource G sites q),
    S.card <= (S.biUnion
      (lpReplicaAggregatePooledNeighbors G sites hsite q)).card


structure LPReplicaAggregatePooledMatching
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  output : LPReplicaAggregateDecoratedSource G sites q ->
    LPReplicaAggregateDecoratedTarget G sites q
  output_injective : Function.Injective output
  output_related : forall z,
    LPReplicaAggregatePooledRelated G sites hsite q z (output z)


theorem nonempty_lpReplicaAggregatePooledMatching_iff_hall
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Nonempty (LPReplicaAggregatePooledMatching G sites hsite q) <->
      LPReplicaAggregatePooledHall G sites hsite q := by
  classical
  constructor
  · rintro ⟨m⟩
    unfold LPReplicaAggregatePooledHall
    apply (Finset.all_card_le_biUnion_card_iff_exists_injective
      (lpReplicaAggregatePooledNeighbors G sites hsite q)).mpr
    refine ⟨m.output, m.output_injective, ?_⟩
    intro z
    simp only [lpReplicaAggregatePooledNeighbors,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact m.output_related z
  · intro hHall
    have hHall' : forall S : Finset
        (LPReplicaAggregateDecoratedSource G sites q),
        S.card <= (S.biUnion
          (lpReplicaAggregatePooledNeighbors G sites hsite q)).card := by
      simpa only [LPReplicaAggregatePooledHall] using hHall
    obtain ⟨move, hmove, hmem⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective
        (lpReplicaAggregatePooledNeighbors G sites hsite q)).mp hHall'
    refine ⟨{
      output := move
      output_injective := hmove
      output_related := ?_
    }⟩
    intro z
    have hz := hmem z
    simpa only [lpReplicaAggregatePooledNeighbors,
      Finset.mem_filter, Finset.mem_univ, true_and] using hz



theorem lpReplicaAggregateDecoratedInjection_of_pooledMatching
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (m : LPReplicaAggregatePooledMatching G sites hsite q) :
    LPReplicaAggregateDecoratedInjection G sites q :=
  ⟨m.output, m.output_injective⟩



theorem lpReplicaAggregateProfileOrbitInequality_of_aggregatePooledHall
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hHall : ∀ q, LPReplicaAggregatePooledHall G sites hsite q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_aggregateDecoratedInjections
    G sites beta J hf r hbeta hJ hhf hr
  intro q
  have hm :=
    (nonempty_lpReplicaAggregatePooledMatching_iff_hall
      G sites hsite q).mpr (hHall q)
  exact lpReplicaAggregateDecoratedInjection_of_pooledMatching
    G sites hsite q (Classical.choice hm)



theorem lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_aggregatePooledHall
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hHall : ∀ q, LPReplicaAggregatePooledHall G sites hsite q) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    (∑ i : I, ∑ j : I,
      lpMatchingFiveCurrentCoefficient H beta Jr
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0 := by
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  have horbit :=
    lpReplicaAggregateProfileOrbitInequality_of_aggregatePooledHall
      G sites hsite beta J hf r hbeta hJ hhf hr hHall
  have hmatch := lpReplicaMatchingDisconn_le_of_profileOrbit
    G sites beta J hf r hbeta hJ hhf hr horbit
  dsimp only at hmatch
  apply (lpMatchingFiveCurrentCoefficient_sum_nonpos_iff
    H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by
        simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])).mpr
  rw [lpGhostCurrentSquareGap_eq_emptyDisconn H beta Jr
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by
      simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])]
  exact hmatch


noncomputable def lpReplicaAggregateDecoratedSourceCrossTrace
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    LPReplicaOrbitFourColorSlotState G sites q :=
  lpReplicaOffdiagDecoratedSourceCrossTrace G sites z.1 z.2.1 q z.2.2.2



noncomputable def lpReplicaAggregateDecoratedTargetCrossTrace
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    LPReplicaOrbitFourColorSlotState G sites q :=
  lpReplicaOffdiagDecoratedTargetCrossTrace
    G sites y.2.1 y.2.2.1 q (Sum.inl y.2.2.2)




def LPReplicaAggregateCrossToggleRelated
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q) : Prop :=
  lpReplicaAggregateDecoratedTargetCrossTrace G sites q y =
    lpReplicaAggregateDecoratedSourceCrossTrace G sites q z


noncomputable def lpReplicaAggregateCrossToggleNeighbors
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    Finset (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  exact Finset.univ.filter fun y =>
    LPReplicaAggregateCrossToggleRelated G sites q z y


noncomputable def LPReplicaAggregateCrossToggleHall
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop := by
  classical
  exact forall S : Finset (LPReplicaAggregateDecoratedSource G sites q),
    S.card <= (S.biUnion
      (lpReplicaAggregateCrossToggleNeighbors G sites q)).card


structure LPReplicaAggregateCrossToggleMatching
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  output : LPReplicaAggregateDecoratedSource G sites q ->
    LPReplicaAggregateDecoratedTarget G sites q
  output_injective : Function.Injective output
  output_related : forall z,
    LPReplicaAggregateCrossToggleRelated G sites q z (output z)


theorem nonempty_lpReplicaAggregateCrossToggleMatching_iff_hall
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Nonempty (LPReplicaAggregateCrossToggleMatching G sites q) <->
      LPReplicaAggregateCrossToggleHall G sites q := by
  classical
  constructor
  · rintro ⟨m⟩
    unfold LPReplicaAggregateCrossToggleHall
    apply (Finset.all_card_le_biUnion_card_iff_exists_injective
      (lpReplicaAggregateCrossToggleNeighbors G sites q)).mpr
    refine ⟨m.output, m.output_injective, ?_⟩
    intro z
    simp only [lpReplicaAggregateCrossToggleNeighbors,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact m.output_related z
  · intro hHall
    have hHall' : forall S : Finset
        (LPReplicaAggregateDecoratedSource G sites q),
        S.card <= (S.biUnion
          (lpReplicaAggregateCrossToggleNeighbors G sites q)).card := by
      simpa only [LPReplicaAggregateCrossToggleHall] using hHall
    obtain ⟨move, hmove, hmem⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective
        (lpReplicaAggregateCrossToggleNeighbors G sites q)).mp hHall'
    refine ⟨{
      output := move
      output_injective := hmove
      output_related := ?_
    }⟩
    intro z
    have hz := hmem z
    simpa only [lpReplicaAggregateCrossToggleNeighbors,
      Finset.mem_filter, Finset.mem_univ, true_and] using hz



theorem lpReplicaAggregateDecoratedInjection_of_crossToggleMatching
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (m : LPReplicaAggregateCrossToggleMatching G sites q) :
    LPReplicaAggregateDecoratedInjection G sites q :=
  ⟨m.output, m.output_injective⟩



theorem lpReplicaAggregateProfileOrbitInequality_of_aggregateCrossToggleHall
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hHall : ∀ q, LPReplicaAggregateCrossToggleHall G sites q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_aggregateDecoratedInjections
    G sites beta J hf r hbeta hJ hhf hr
  intro q
  have hm :=
    (nonempty_lpReplicaAggregateCrossToggleMatching_iff_hall
      G sites q).mpr (hHall q)
  exact lpReplicaAggregateDecoratedInjection_of_crossToggleMatching
    G sites q (Classical.choice hm)





def LPReplicaAggregateConnectedSeamRelated
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q) : Prop :=
  StatMech.Sharpness.CurrentConnected (lpReplicaCurrentGraph G sites)
    (StatMech.Sharpness.ofEdgeFun
      (lpReplicaCurrentGraph G sites) z.2.2.2.1.1.1)
    (lpReplicaCurrentLeft sites y.2.1)
    (lpReplicaCurrentRight sites y.2.1)


noncomputable def lpReplicaAggregateConnectedSeamNeighbors
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    Finset (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  exact Finset.univ.filter fun y =>
    LPReplicaAggregateConnectedSeamRelated G sites q z y


noncomputable def LPReplicaAggregateConnectedSeamHall
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop := by
  classical
  exact forall S : Finset (LPReplicaAggregateDecoratedSource G sites q),
    S.card <= (S.biUnion
      (lpReplicaAggregateConnectedSeamNeighbors G sites q)).card


theorem lpReplicaAggregateDecoratedInjection_of_connectedSeamHall
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hHall : LPReplicaAggregateConnectedSeamHall G sites q) :
    LPReplicaAggregateDecoratedInjection G sites q := by
  classical
  have hHall' : forall S : Finset
      (LPReplicaAggregateDecoratedSource G sites q),
      S.card <= (S.biUnion
        (lpReplicaAggregateConnectedSeamNeighbors G sites q)).card := by
    simpa only [LPReplicaAggregateConnectedSeamHall] using hHall
  obtain ⟨move, hmove, _⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (lpReplicaAggregateConnectedSeamNeighbors G sites q)).mp hHall'
  exact ⟨move, hmove⟩



theorem lpReplicaAggregateProfileOrbitInequality_of_connectedSeamHall
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hHall : ∀ q, LPReplicaAggregateConnectedSeamHall G sites q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_aggregateDecoratedInjections
    G sites beta J hf r hbeta hJ hhf hr
  intro q
  exact lpReplicaAggregateDecoratedInjection_of_connectedSeamHall
    G sites q (hHall q)



theorem lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_connectedSeamHall
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hHall : ∀ q, LPReplicaAggregateConnectedSeamHall G sites q) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    (∑ i : I, ∑ j : I,
      lpMatchingFiveCurrentCoefficient H beta Jr
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0 := by
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  have horbit := lpReplicaAggregateProfileOrbitInequality_of_connectedSeamHall
    G sites beta J hf r hbeta hJ hhf hr hHall
  have hmatch := lpReplicaMatchingDisconn_le_of_profileOrbit
    G sites beta J hf r hbeta hJ hhf hr horbit
  dsimp only at hmatch
  apply (lpMatchingFiveCurrentCoefficient_sum_nonpos_iff
    H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by
        simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])).mpr
  rw [lpGhostCurrentSquareGap_eq_emptyDisconn H beta Jr
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by
      simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])]
  exact hmatch






def LPReplicaAggregateSelectedSeamRelated
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q) : Prop :=
  lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q z = y.2.1


noncomputable def lpReplicaAggregateSelectedSeamNeighbors
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    Finset (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  exact Finset.univ.filter fun y =>
    LPReplicaAggregateSelectedSeamRelated G sites hsite q z y


noncomputable def LPReplicaAggregateSelectedSeamHall
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop := by
  classical
  exact forall S : Finset (LPReplicaAggregateDecoratedSource G sites q),
    S.card <= (S.biUnion
      (lpReplicaAggregateSelectedSeamNeighbors G sites hsite q)).card



def LPReplicaAggregateSelectedSeamCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop :=
  forall k : I,
    Fintype.card {z : LPReplicaAggregateDecoratedSource G sites q //
      lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q z = k} <=
    Fintype.card {y : LPReplicaAggregateDecoratedTarget G sites q //
      y.2.1 = k}



theorem lpReplicaAggregateSelectedSeamHall_iff_capacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaAggregateSelectedSeamHall G sites hsite q <->
      LPReplicaAggregateSelectedSeamCapacity G sites hsite q := by
  classical
  let f := lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q
  let g := fun y : LPReplicaAggregateDecoratedTarget G sites q => y.2.1
  have hequal := Fintype.hall_equalFiber_iff_card_fibers f g
  constructor
  · intro hHall
    apply hequal.mp
    intro S
    have hS := hHall S
    have hneighbors : S.biUnion
        (lpReplicaAggregateSelectedSeamNeighbors G sites hsite q) =
        Finset.univ.filter fun y =>
          ∃ z, z ∈ S ∧ f z = g y := by
      ext y
      simp only [lpReplicaAggregateSelectedSeamNeighbors,
        LPReplicaAggregateSelectedSeamRelated, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_univ, true_and, f, g]
    rwa [hneighbors] at hS
  · intro hcapacity
    have hfiber : forall k : I,
        Fintype.card {z : LPReplicaAggregateDecoratedSource G sites q //
          f z = k} <=
        Fintype.card {y : LPReplicaAggregateDecoratedTarget G sites q //
          g y = k} := by
      simpa only [LPReplicaAggregateSelectedSeamCapacity, f, g] using hcapacity
    have hHall := hequal.mpr hfiber
    intro S
    have hS := hHall S
    have hneighbors : S.biUnion
        (lpReplicaAggregateSelectedSeamNeighbors G sites hsite q) =
        Finset.univ.filter fun y =>
          ∃ z, z ∈ S ∧ f z = g y := by
      ext y
      simp only [lpReplicaAggregateSelectedSeamNeighbors,
        LPReplicaAggregateSelectedSeamRelated, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_univ, true_and, f, g]
    rwa [hneighbors]



theorem lpReplicaAggregateSelectedSeamRelated_connected
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (hrelated : LPReplicaAggregateSelectedSeamRelated
      G sites hsite q z y) :
    LPReplicaAggregateConnectedSeamRelated G sites q z y := by
  unfold LPReplicaAggregateSelectedSeamRelated at hrelated
  unfold LPReplicaAggregateConnectedSeamRelated
  rw [← hrelated]
  exact lpReplicaAggregateDecoratedSourceSelectedSeam_connected
    G sites hsite q z



theorem lpReplicaAggregateConnectedSeamHall_of_selectedSeamHall
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hHall : LPReplicaAggregateSelectedSeamHall G sites hsite q) :
    LPReplicaAggregateConnectedSeamHall G sites q := by
  classical
  intro S
  calc
    S.card <= (S.biUnion
        (lpReplicaAggregateSelectedSeamNeighbors G sites hsite q)).card :=
      hHall S
    _ <= (S.biUnion
        (lpReplicaAggregateConnectedSeamNeighbors G sites q)).card := by
      apply Finset.card_le_card
      intro y hy
      simp only [Finset.mem_biUnion] at hy ⊢
      obtain ⟨z, hz, hyz⟩ := hy
      refine ⟨z, hz, ?_⟩
      simp only [lpReplicaAggregateSelectedSeamNeighbors,
        Finset.mem_filter, Finset.mem_univ, true_and] at hyz
      simp only [lpReplicaAggregateConnectedSeamNeighbors,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact lpReplicaAggregateSelectedSeamRelated_connected
        G sites hsite q z y hyz



theorem lpReplicaAggregateDecoratedInjection_of_selectedSeamCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcapacity : LPReplicaAggregateSelectedSeamCapacity G sites hsite q) :
    LPReplicaAggregateDecoratedInjection G sites q := by
  classical
  have hHall := (lpReplicaAggregateSelectedSeamHall_iff_capacity
    G sites hsite q).mpr hcapacity
  have hHall' : forall S : Finset
      (LPReplicaAggregateDecoratedSource G sites q),
      S.card <= (S.biUnion
        (lpReplicaAggregateSelectedSeamNeighbors G sites hsite q)).card := by
    simpa only [LPReplicaAggregateSelectedSeamHall] using hHall
  obtain ⟨move, hmove, _⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (lpReplicaAggregateSelectedSeamNeighbors G sites hsite q)).mp hHall'
  exact ⟨move, hmove⟩



theorem lpReplicaAggregateProfileOrbitInequality_of_selectedSeamCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hcapacity : ∀ q,
      LPReplicaAggregateSelectedSeamCapacity G sites hsite q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_aggregateDecoratedInjections
    G sites beta J hf r hbeta hJ hhf hr
  intro q
  exact lpReplicaAggregateDecoratedInjection_of_selectedSeamCapacity
    G sites hsite q (hcapacity q)



theorem lpReplicaMatchingFiveCurrentCoefficient_sum_nonpos_of_selectedSeamCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hcapacity : ∀ q,
      LPReplicaAggregateSelectedSeamCapacity G sites hsite q) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    (∑ i : I, ∑ j : I,
      lpMatchingFiveCurrentCoefficient H beta Jr
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 i j) <= 0 := by
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  have horbit :=
    lpReplicaAggregateProfileOrbitInequality_of_selectedSeamCapacity
      G sites hsite beta J hf r hbeta hJ hhf hr hcapacity
  have hmatch := lpReplicaMatchingDisconn_le_of_profileOrbit
    G sites beta J hf r hbeta hJ hhf hr horbit
  dsimp only at hmatch
  apply (lpMatchingFiveCurrentCoefficient_sum_nonpos_iff
    H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by
        simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])).mpr
  rw [lpGhostCurrentSquareGap_eq_emptyDisconn H beta Jr
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by
      simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])]
  exact hmatch



noncomputable def lpReplicaAggregateSelectedTargetFiberEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) (k : I) :
    {y : LPReplicaAggregateDecoratedTarget G sites q // y.2.1 = k} ≃
      Fin 2 × Sigma fun j : I =>
        LPReplicaDecoratedOrbitAtom G sites
          (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k)
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q := by
  classical
  refine {
    toFun := ?_
    invFun := ?_
    left_inv := ?_
    right_inv := ?_
  }
  · rintro ⟨⟨b, ⟨i, ⟨j, atom⟩⟩⟩, hi⟩
    dsimp only at hi
    subst i
    exact ⟨b, ⟨j, atom⟩⟩
  · rintro ⟨b, ⟨j, atom⟩⟩
    exact ⟨⟨b, ⟨k, ⟨j, atom⟩⟩⟩, rfl⟩
  · rintro ⟨⟨b, ⟨i, ⟨j, atom⟩⟩⟩, hi⟩
    dsimp only at hi
    subst i
    rfl
  · rintro ⟨b, ⟨j, atom⟩⟩
    rfl



theorem card_lpReplicaAggregateSelectedTargetFiber
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) (k : I) :
    Fintype.card
        {y : LPReplicaAggregateDecoratedTarget G sites q // y.2.1 = k} =
      ∑ j : I, 2 * Fintype.card
        (LPReplicaDecoratedOrbitAtom G sites
          (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k)
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q) := by
  rw [Fintype.card_congr
    (lpReplicaAggregateSelectedTargetFiberEquiv G sites q k),
    Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma,
    Finset.mul_sum]




theorem lpReplicaAggregateSelectedSeamCapacity_iff_explicit
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaAggregateSelectedSeamCapacity G sites hsite q <->
      forall k : I,
        Fintype.card {z : LPReplicaAggregateDecoratedSource G sites q //
            lpReplicaAggregateDecoratedSourceSelectedSeam
              G sites hsite q z = k} <=
          ∑ j : I, 2 * Fintype.card
            (LPReplicaDecoratedOrbitAtom G sites
              (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites)
                (lpReplicaCurrentRight sites) k)
              (lpMatchingSeamSource
                  (lpReplicaCurrentLeft sites)
                  (lpReplicaCurrentRight sites) j ∆
                lpMatchingGhostSource
                  (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                  lpReplicaCurrentGhost1) q) := by
  unfold LPReplicaAggregateSelectedSeamCapacity
  simp_rw [card_lpReplicaAggregateSelectedTargetFiber]

end

end StatMech.Ising
