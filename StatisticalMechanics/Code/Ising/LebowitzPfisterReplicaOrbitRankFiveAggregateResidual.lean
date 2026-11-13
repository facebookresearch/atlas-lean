/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked












namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveResidualDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



def LPReplicaAggregateRankFiveResidualCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop :=
  Fintype.card
      (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) <=
    Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) -
      Fintype.card
        (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q)



theorem lpReplicaAggregateRankFiveResidualCapacity_iff_card_le_target
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    LPReplicaAggregateRankFiveResidualCapacity G sites q <->
      Fintype.card (LPReplicaAggregateDecoratedSource G sites q) <=
        Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
  let H := Fintype.card
    (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q)
  let U := Fintype.card
    (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
  let T := Fintype.card (LPReplicaAggregateDecoratedTarget G sites q)
  have hhandled : H <= T := by
    simpa only [H, T] using
      card_lpReplicaAggregateLowOrResolvableHighSourceRankFive_le_target
        G sites hsite q hcard
  have hsource :
      Fintype.card (LPReplicaAggregateDecoratedSource G sites q) = H + U := by
    simpa only [H, U] using
      card_lpReplicaAggregateDecoratedSource_rankFive_eq_handled_add_unmarked
        G sites q
  constructor
  · intro hresidual
    have hUH : U + H <= T := by
      apply Nat.add_le_of_le_sub hhandled
      simpa only [LPReplicaAggregateRankFiveResidualCapacity, U, T, H] using
        hresidual
    rw [hsource]
    simpa only [Nat.add_comm] using hUH
  · intro hfull
    have hHU : H + U <= T := by
      rwa [hsource] at hfull
    unfold LPReplicaAggregateRankFiveResidualCapacity
    apply Nat.le_sub_of_add_le
    simpa only [H, U, T, Nat.add_comm] using hHU



noncomputable def lpReplicaAggregateRankFiveHandledTargetImage
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    Finset (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  exact Finset.univ.image
    (lpReplicaAggregateLowOrResolvableHighRankFiveEmbedding
      G sites hsite q hcard)




noncomputable def LPReplicaAggregateRankFiveSelectedResidualCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) : Prop := by
  classical
  exact forall k : I,
    Fintype.card
        {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q //
          lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q
            (z.toAggregate G sites q) = k} <=
      Fintype.card
        {y : {y : LPReplicaAggregateDecoratedTarget G sites q //
          y ∉ lpReplicaAggregateRankFiveHandledTargetImage
            G sites hsite q hcard} // y.1.2.1 = k}



theorem card_lpReplicaAggregateRankFiveHandledTargetImage
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    (lpReplicaAggregateRankFiveHandledTargetImage
      G sites hsite q hcard).card =
      Fintype.card
        (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q) := by
  classical
  unfold lpReplicaAggregateRankFiveHandledTargetImage
  rw [Finset.card_image_of_injective _
    (lpReplicaAggregateLowOrResolvableHighRankFiveEmbedding
      G sites hsite q hcard).injective,
    Finset.card_univ]



theorem lpReplicaAggregateRankFiveResidualCapacity_of_selected
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (hselected : LPReplicaAggregateRankFiveSelectedResidualCapacity
      G sites hsite q hcard) :
    LPReplicaAggregateRankFiveResidualCapacity G sites q := by
  classical
  let A := LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q
  let used := lpReplicaAggregateRankFiveHandledTargetImage
    G sites hsite q hcard
  let B := {y : LPReplicaAggregateDecoratedTarget G sites q // y ∉ used}
  let f : A -> I := fun z =>
    lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q
      (z.toAggregate G sites q)
  let g : B -> I := fun y => y.1.2.1
  have hfiber : forall k : I,
      Fintype.card {z : A // f z = k} <=
        Fintype.card {y : B // g y = k} := by
    simpa only [LPReplicaAggregateRankFiveSelectedResidualCapacity,
      A, B, f, g, used] using hselected
  have hhall :=
    (Fintype.hall_equalFiber_iff_card_fibers f g).mpr hfiber
  have hAB : Fintype.card A <= Fintype.card B := by
    calc
      Fintype.card A = (Finset.univ : Finset A).card :=
        Finset.card_univ.symm
      _ <= (Finset.univ.filter fun b : B =>
          exists a, a ∈ (Finset.univ : Finset A) /\ f a = g b).card :=
        hhall Finset.univ
      _ <= (Finset.univ : Finset B).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = Fintype.card B := Finset.card_univ
  have hB : Fintype.card B =
      Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) -
        Fintype.card
          (LPReplicaAggregateLowOrResolvableHighSourceRankFive
            G sites q) := by
    rw [Fintype.card_subtype]
    change (Finset.univ.filter fun y :
        LPReplicaAggregateDecoratedTarget G sites q => y ∉ used).card = _
    have hfilter : (Finset.univ.filter fun y :
        LPReplicaAggregateDecoratedTarget G sites q => y ∉ used) =
        Finset.univ \ used := by
      ext y
      simp
    rw [hfilter, Finset.card_sdiff]
    rw [Finset.inter_eq_left.mpr (Finset.subset_univ used),
      Finset.card_univ,
      card_lpReplicaAggregateRankFiveHandledTargetImage
        G sites hsite q hcard]
  unfold LPReplicaAggregateRankFiveResidualCapacity
  change Fintype.card A <= _
  rw [← hB]
  exact hAB



noncomputable def lpReplicaAggregateRankFiveEmbedding_of_residualCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (hresidual : LPReplicaAggregateRankFiveResidualCapacity G sites q) :
    LPReplicaAggregateDecoratedSource G sites q ↪
      LPReplicaAggregateDecoratedTarget G sites q := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  exact
    (lpReplicaAggregateRankFiveResidualCapacity_iff_card_le_target
      G sites hsite q hcard).mp hresidual



noncomputable def lpReplicaAggregateRankFiveEmbedding_of_selectedResidualCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (hselected : LPReplicaAggregateRankFiveSelectedResidualCapacity
      G sites hsite q hcard) :
    LPReplicaAggregateDecoratedSource G sites q ↪
      LPReplicaAggregateDecoratedTarget G sites q :=
  lpReplicaAggregateRankFiveEmbedding_of_residualCapacity
    G sites hsite q hcard
      (lpReplicaAggregateRankFiveResidualCapacity_of_selected
        G sites hsite q hcard hselected)



theorem lpReplicaAggregateProfileOrbitInequality_rankFive_of_residualCapacity
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (hhf : forall x, 0 <= hf x) (hr : 0 <= r)
    (hresidual : forall q,
      Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5 ->
        LPReplicaAggregateRankFiveResidualCapacity G sites q)
    (hrank : forall q,
      Fintype.card (LPReplicaOrbitCommonSlot G sites q) ≠ 5 ->
        LPReplicaAggregateDecoratedInjection G sites q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_aggregateDecoratedInjections
    G sites beta J hf r hbeta hJ hhf hr
  intro q
  by_cases hcard : Fintype.card
      (LPReplicaOrbitCommonSlot G sites q) = 5
  · let e := lpReplicaAggregateRankFiveEmbedding_of_residualCapacity
      G sites hsite q hcard (hresidual q hcard)
    exact ⟨e, e.injective⟩
  · exact hrank q hcard

end

end StatMech.Ising
