/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching
import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateFiber










open Finset

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveAggregateBoundDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


abbrev LPReplicaAggregateSourceCrossTraceFiber
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :=
  {z : LPReplicaAggregateDecoratedSource G sites q //
    lpReplicaAggregateDecoratedSourceCrossTrace G sites q z = u}

noncomputable instance instFintypeLPReplicaAggregateSourceCrossTraceFiber
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Fintype (LPReplicaAggregateSourceCrossTraceFiber G sites q u) :=
  Fintype.ofFinite _


noncomputable def lpReplicaOffdiagRankFiveCrossTraceFiberEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    {z // z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites i j q u} ↪ Fin 4 := by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_coe] using
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_card_le_four
      G sites hsite hij q hcard u)



noncomputable def lpReplicaAggregateRankFiveSourceKey
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    LPReplicaAggregateSourceCrossTraceFiber G sites q u ->
      I × (I × Fin 4) := fun z =>
  let hij := lpReplicaAggregateDecoratedSource_indices_ne G sites q z.1
  let atom : {a // a ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites z.1.1 z.1.2.1 q u} := ⟨z.1.2.2.2, by
    simp only [lpReplicaOffdiagDecoratedSourceCrossTraceFiber,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact z.2⟩
  (z.1.1, (z.1.2.1,
    lpReplicaOffdiagRankFiveCrossTraceFiberEmbedding
      G sites hsite hij q hcard u atom))

set_option maxHeartbeats 800000 in


theorem lpReplicaAggregateRankFiveSourceKey_injective
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Function.Injective
      (lpReplicaAggregateRankFiveSourceKey
        G sites hsite q hcard u) := by
  classical
  rintro ⟨⟨i, j, wi, a⟩, ha⟩ ⟨⟨k, l, wk, b⟩, hb⟩ hkey
  have hi : i = k := congrArg Prod.fst hkey
  have hj : j = l := congrArg (fun x => x.2.1) hkey
  subst k
  subst l
  have hlabel := congrArg (fun x => x.2.2) hkey
  have ha' : a ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites i j q u := by
    simp only [lpReplicaOffdiagDecoratedSourceCrossTraceFiber,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha
  have hb' : b ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites i j q u := by
    simp only [lpReplicaOffdiagDecoratedSourceCrossTraceFiber,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact hb
  have hatomSubtype :
      (⟨a, ha'⟩ : {x // x ∈
        lpReplicaOffdiagDecoratedSourceCrossTraceFiber
          G sites i j q u}) = ⟨b, hb'⟩ := by
    apply (lpReplicaOffdiagRankFiveCrossTraceFiberEmbedding
      G sites hsite
        (lpReplicaAggregateDecoratedSource_indices_ne
          G sites q ⟨i, j, wi, a⟩)
        q hcard u).injective
    simpa only [lpReplicaAggregateRankFiveSourceKey] using hlabel
  have hab : a = b := congrArg Subtype.val hatomSubtype
  subst b
  have hij := lpReplicaAggregateDecoratedSource_indices_ne
    G sites q ⟨i, j, wi, a⟩
  have hw : wi = wk := by
    apply Fin.ext
    have hwi := wi.isLt
    have hwk := wk.isLt
    simp only [if_neg hij] at hwi hwk
    omega
  subst wk
  rfl



theorem card_lpReplicaAggregateSourceCrossTraceFiber_rank_five_le
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Fintype.card (LPReplicaAggregateSourceCrossTraceFiber G sites q u) <=
      Fintype.card I * (Fintype.card I * 4) := by
  calc
    Fintype.card (LPReplicaAggregateSourceCrossTraceFiber G sites q u) <=
        Fintype.card (I × (I × Fin 4)) :=
      Fintype.card_le_of_injective
        (lpReplicaAggregateRankFiveSourceKey G sites hsite q hcard u)
        (lpReplicaAggregateRankFiveSourceKey_injective
          G sites hsite q hcard u)
    _ = Fintype.card I * (Fintype.card I * 4) := by
      simp only [Fintype.card_prod, Fintype.card_fin]

end

end StatMech.Ising
