/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation











open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveUnmarkedDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


def LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) : Prop :=
  LPReplicaOffdiagDecoratedSource.IsSaturatedRankFive G sites i j q z ∧
    (forall c : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1,
      c.1.1 ≠ lpReplicaCurrentSeamEdge sites i) ∧
    (forall c : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1,
      c.1.1 ≠ lpReplicaCurrentSeamEdge sites j)



theorem LPReplicaOffdiagDecoratedSource.resolvable_or_unmarkedSaturated_of_highRow
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh : LPReplicaOffdiagDecoratedSource.IsHighRowRankFive
      G sites i j q z) :
    LPReplicaOffdiagDecoratedSource.IsResolvableHighRowRankFive
        G sites i j q z ∨
      LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive
        G sites i j q z := by
  classical
  by_cases hsat : LPReplicaOffdiagDecoratedSource.IsSaturatedRankFive
      G sites i j q z
  · by_cases hi : exists c : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1,
        c.1.1 = lpReplicaCurrentSeamEdge sites i
    · exact Or.inl ⟨hhigh, fun _ => Or.inl hi⟩
    · by_cases hj : exists c : StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) z.1.1.1,
          c.1.1 = lpReplicaCurrentSeamEdge sites j
      · exact Or.inl ⟨hhigh, fun _ => Or.inr hj⟩
      · simp only [not_exists] at hi hj
        exact Or.inr ⟨hsat, hi, hj⟩
  · exact Or.inl ⟨hhigh, fun hs => (hsat hs).elim⟩



theorem LPReplicaOffdiagDecoratedSource.low_or_resolvable_or_unmarkedSaturated_rankFive
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q z ∨
      LPReplicaOffdiagDecoratedSource.IsResolvableHighRowRankFive
          G sites i j q z ∨
        LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive
          G sites i j q z := by
  classical
  let u := lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z
  have hz : z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites i j q u := by
    simp [lpReplicaOffdiagDecoratedSourceCrossTraceFiber, u]
  rw [lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_eq_low_union_high
    G sites hsite hij q hcard u] at hz
  unfold lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowOrHighRankFive at hz
  rcases Finset.mem_union.mp hz with hlow | hhigh
  · exact Or.inl (Finset.mem_filter.mp hlow).2
  · rcases LPReplicaOffdiagDecoratedSource.resolvable_or_unmarkedSaturated_of_highRow
        G sites i j q z (Finset.mem_filter.mp hhigh).2 with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)



noncomputable def lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact Finset.univ \
    lpReplicaOffdiagLowOrResolvableHighSourcesRankFive G sites i j q



theorem LPReplicaOffdiagDecoratedSource.isUnmarkedSaturatedRankFive_of_mem_complement
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hz : z ∈ lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive
      G sites i j q) :
    LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive
      G sites i j q z := by
  classical
  have hz' : z ∈ Finset.univ \
      lpReplicaOffdiagLowOrResolvableHighSourcesRankFive G sites i j q := by
    simpa only [lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive] using hz
  have hnot := (Finset.mem_sdiff.mp hz').2
  rcases LPReplicaOffdiagDecoratedSource.low_or_resolvable_or_unmarkedSaturated_rankFive
      G sites hsite hij q hcard z with hlow | hresolve | hunmarked
  · exfalso
    apply hnot
    apply Finset.mem_union_left
    simp [lpReplicaOffdiagLowRowSourcesRankFive, hlow]
  · exfalso
    apply hnot
    apply Finset.mem_union_right
    simp [lpReplicaOffdiagResolvableHighRowSourcesRankFive, hresolve]
  · exact hunmarked



theorem lpReplicaAggregateDecoratedSourceSelectedSeam_ne_left_of_unmarkedSaturated
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (hz : LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive
      G sites z.1 z.2.1 q z.2.2.2) :
    lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q z ≠ z.1 := by
  obtain ⟨c, hc⟩ :=
    lpReplicaAggregateDecoratedSourceSelectedSeam_exists_copy
      G sites hsite q z
  intro hk
  apply hz.2.1 c
  exact hc.trans (congrArg (lpReplicaCurrentSeamEdge sites) hk)



theorem lpReplicaAggregateDecoratedSourceSelectedSeam_ne_right_of_unmarkedSaturated
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q)
    (hz : LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive
      G sites z.1 z.2.1 q z.2.2.2) :
    lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q z ≠
      z.2.1 := by
  obtain ⟨c, hc⟩ :=
    lpReplicaAggregateDecoratedSourceSelectedSeam_exists_copy
      G sites hsite q z
  intro hk
  apply hz.2.2 c
  exact hc.trans (congrArg (lpReplicaCurrentSeamEdge sites) hk)


def LPReplicaAggregateUnmarkedSaturatedSourceRankFive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Sigma fun i : I => Sigma fun j : I =>
    Fin (if i = j then 0 else 1) ×
      ↑(lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive G sites i j q)

noncomputable instance
    instFintypeLPReplicaAggregateUnmarkedSaturatedSourceRankFive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) := by
  unfold LPReplicaAggregateUnmarkedSaturatedSourceRankFive
  infer_instance


theorem card_lpReplicaAggregateUnmarkedSaturatedSourceRankFive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card
        (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) =
      ∑ i : I, ∑ j : I, if i = j then 0 else
        (lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive
          G sites i j q).card := by
  classical
  unfold LPReplicaAggregateUnmarkedSaturatedSourceRankFive
  change Fintype.card
      (Sigma fun i : I => Sigma fun j : I =>
        Fin (if i = j then 0 else 1) ×
          ↑(lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive
            G sites i j q)) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.card_prod, Fintype.card_coe]
  by_cases hij : i = j <;> simp [hij]



def LPReplicaAggregateUnmarkedSaturatedSourceRankFive.toAggregate
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    LPReplicaAggregateDecoratedSource G sites q :=
  ⟨z.1, z.2.1, z.2.2.1, z.2.2.2.1⟩


theorem LPReplicaAggregateUnmarkedSaturatedSourceRankFive.toAggregate_injective
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Injective
      (LPReplicaAggregateUnmarkedSaturatedSourceRankFive.toAggregate
        G sites q) := by
  intro z w h
  rcases z with ⟨i, j, b, z, hz⟩
  rcases w with ⟨i', j', b', w, hw⟩
  simp only [LPReplicaAggregateUnmarkedSaturatedSourceRankFive.toAggregate]
    at h
  cases h
  rfl



theorem lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    let a := z.toAggregate G sites q
    lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q a ≠ a.1 ∧
      lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q a ≠
        a.2.1 := by
  classical
  let a := z.toAggregate G sites q
  have hij : z.1 ≠ z.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hunmarked :=
    LPReplicaOffdiagDecoratedSource.isUnmarkedSaturatedRankFive_of_mem_complement
      G sites hsite hij q hcard z.2.2.2.1 z.2.2.2.2
  exact ⟨
    (lpReplicaAggregateDecoratedSourceSelectedSeam_ne_left_of_unmarkedSaturated
      G sites hsite q a hunmarked),
    (lpReplicaAggregateDecoratedSourceSelectedSeam_ne_right_of_unmarkedSaturated
      G sites hsite q a hunmarked)⟩



theorem lpReplicaOffdiag_rankFive_handled_union_unmarkedSaturated
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    z ∈ lpReplicaOffdiagLowOrResolvableHighSourcesRankFive G sites i j q ∨
      z ∈ lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive
        G sites i j q := by
  classical
  by_cases hz : z ∈ lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
      G sites i j q
  · exact Or.inl hz
  · exact Or.inr (by
      simp only [lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive,
        Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact hz)


theorem lpReplicaOffdiag_rankFive_card_handled_add_unmarkedSaturated
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
        G sites i j q).card +
      (lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive
        G sites i j q).card =
      Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive,
    Finset.union_eq_left.mpr (Finset.subset_univ _), Nat.add_comm] using
    (Finset.card_sdiff_add_card
      (s := (Finset.univ : Finset
        (LPReplicaOffdiagDecoratedSource G sites i j q)))
      (t := lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
        G sites i j q))



theorem card_lpReplicaAggregateDecoratedSource_rankFive_eq_handled_add_unmarked
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaAggregateDecoratedSource G sites q) =
      Fintype.card
          (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q) +
        Fintype.card
          (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) := by
  classical
  rw [card_lpReplicaAggregateDecoratedSource,
    card_lpReplicaAggregateLowOrResolvableHighSourceRankFive,
    card_lpReplicaAggregateUnmarkedSaturatedSourceRankFive,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, ↓reduceIte]
    exact (lpReplicaOffdiag_rankFive_card_handled_add_unmarkedSaturated
      G sites i j q).symm


theorem lpReplicaOffdiag_rankFive_handled_disjoint_unmarkedSaturated
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Disjoint
      (lpReplicaOffdiagLowOrResolvableHighSourcesRankFive G sites i j q)
      (lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive G sites i j q) := by
  classical
  simpa only [lpReplicaOffdiagUnmarkedSaturatedSourcesRankFive] using
    (Finset.disjoint_sdiff
      (s := lpReplicaOffdiagLowOrResolvableHighSourcesRankFive
        G sites i j q)
      (t := (Finset.univ : Finset
        (LPReplicaOffdiagDecoratedSource G sites i j q))))

end

end StatMech.Ising
