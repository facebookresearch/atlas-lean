/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle











namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

private noncomputable def finiteFiberMultiplicityEmbedding
    {S T : Type*} [Fintype S] [Fintype T]
    (key : S -> T)
    (hfiber : forall target, Fintype.card {s : S // key s = target} <= 2)
    (target : T) : {s : S // key s = target} ↪ Fin 2 := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa using hfiber target



noncomputable def finiteFiberMultiplicityCode
    {S T : Type*} [Fintype S] [Fintype T]
    (key : S -> T)
    (hfiber : forall target, Fintype.card {s : S // key s = target} <= 2)
    (s : S) : Fin 2 :=
  finiteFiberMultiplicityEmbedding key hfiber (key s) ⟨s, rfl⟩



theorem finiteFiberMultiplicityCode_key_injective
    {S T : Type*} [Fintype S] [Fintype T]
    (key : S -> T)
    (hfiber : forall target, Fintype.card {s : S // key s = target} <= 2) :
    Function.Injective
      (fun s => (finiteFiberMultiplicityCode key hfiber s, key s)) := by
  intro s t hst
  have hkey : key s = key t := congrArg Prod.snd hst
  have hbit : finiteFiberMultiplicityCode key hfiber s =
      finiteFiberMultiplicityCode key hfiber t := congrArg Prod.fst hst
  unfold finiteFiberMultiplicityCode at hbit
  cases hkey
  exact congrArg Subtype.val
    ((finiteFiberMultiplicityEmbedding key hfiber (key s)).injective hbit)



noncomputable def lpReplicaAggregateHandledEmbeddingOfNonstrictKeyFibers
    {S : Type*} [Fintype S]
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (key : S -> LPReplicaAggregateDecoratedTargetBase G sites q)
    (hfiber : forall target,
      Fintype.card {s : S // key s = target} <= 2) :
    S ↪ LPReplicaAggregateDecoratedTarget G sites q :=
  lpReplicaAggregateDecoratedTargetEmbeddingOfMultiplicityPairCode
    G sites q (finiteFiberMultiplicityCode key hfiber) key
      (finiteFiberMultiplicityCode_key_injective key hfiber)



theorem lpReplicaAggregateHandledEmbeddingOfNonstrictKeyFibers_not_strict
    {S : Type*} [Fintype S]
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (key : S -> LPReplicaAggregateDecoratedTargetBase G sites q)
    (hfiber : forall target,
      Fintype.card {s : S // key s = target} <= 2)
    (hnonstrict : forall s,
      ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites q ⟨0, key s⟩) (s : S) :
    ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites q
        (lpReplicaAggregateHandledEmbeddingOfNonstrictKeyFibers
          G sites q key hfiber s) := by
  exact lpReplicaAggregateDecoratedTargetEmbeddingOfMultiplicityPairCode_not_strict
    G sites q (finiteFiberMultiplicityCode key hfiber) key
      (finiteFiberMultiplicityCode_key_injective key hfiber)
      hnonstrict s



noncomputable def
    lpReplicaAggregateRankFiveCombinedEmbeddingOfNonstrictKeyFibers
    {S : Type*} [Fintype S]
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (key : S -> LPReplicaAggregateDecoratedTargetBase G sites q)
    (hfiber : forall target,
      Fintype.card {s : S // key s = target} <= 2)
    (hnonstrict : forall s,
      ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites q ⟨0, key s⟩) :
    S ⊕ LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q ↪
      LPReplicaAggregateDecoratedTarget G sites q := by
  let handled := lpReplicaAggregateHandledEmbeddingOfNonstrictKeyFibers
    G sites q key hfiber
  apply lpReplicaAggregateRankFiveCombinedEmbeddingOfNonstrictEmbedding
    G sites hsite q hcard handled
  intro s
  exact lpReplicaAggregateHandledEmbeddingOfNonstrictKeyFibers_not_strict
    G sites q key hfiber hnonstrict s

end

end StatMech.Ising
