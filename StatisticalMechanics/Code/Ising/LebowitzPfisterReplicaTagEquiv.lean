/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaRowTagged








open Finset

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaTagEquivDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


def lpReplicaTransportTag
    (G : SimpleGraph V) (sites : I -> V)
    {m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    (E : Copy (lpReplicaCurrentGraph G sites) m ≃
      Copy (lpReplicaCurrentGraph G sites) n)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    Copy (lpReplicaCurrentGraph G sites) n -> LPReplicaRowTag :=
  fun c => tag (E.symm c)


theorem lpReplicaCurrentCopies_transportTag
    (G : SimpleGraph V) (sites : I -> V)
    {m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    (E : Copy (lpReplicaCurrentGraph G sites) m ≃
      Copy (lpReplicaCurrentGraph G sites) n)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    lpReplicaCurrentCopies G sites n
        (lpReplicaTransportTag G sites E tag) row current =
      (lpReplicaCurrentCopies G sites m tag row current).map E.toEmbedding := by
  ext c
  simp [lpReplicaCurrentCopies, lpReplicaTransportTag]


theorem lpReplicaRowCopies_transportTag
    (G : SimpleGraph V) (sites : I -> V)
    {m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    (E : Copy (lpReplicaCurrentGraph G sites) m ≃
      Copy (lpReplicaCurrentGraph G sites) n)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    lpReplicaRowCopies G sites n
        (lpReplicaTransportTag G sites E tag) row =
      (lpReplicaRowCopies G sites m tag row).map E.toEmbedding := by
  ext c
  simp [lpReplicaRowCopies, lpReplicaTransportTag]


theorem lpReplicaRowGate_transportTag
    (G : SimpleGraph V) (sites : I -> V)
    {m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    (E : Copy (lpReplicaCurrentGraph G sites) m ≃
      Copy (lpReplicaCurrentGraph G sites) n)
    (hends : forall c,
      endsM (lpReplicaCurrentGraph G sites) n (E c) =
        endsM (lpReplicaCurrentGraph G sites) m c)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag) :
    LPReplicaRowGate G sites n A B
      (lpReplicaTransportTag G sites E tag) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let em := endsM H m
  let en := endsM H n
  have hsources (S : Finset (Copy H m)) :
      RandomCurrent.sources en (S.map E.toEmbedding) =
        RandomCurrent.sources em S := by
    exact randomCurrent_sources_map_embedding em en E.toEmbedding hends S
  have hconn (S : Finset (Copy H m)) (u v : LPReplicaCurrentVertex V) :
      RandomCurrent.connK en (S.map E.toEmbedding) u v <->
        RandomCurrent.connK em S u v := by
    exact randomCurrent_connK_map_embedding em en E.toEmbedding hends S u v
  dsimp only [LPReplicaRowGate] at hgate ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lpReplicaCurrentCopies_transportTag, hsources]
    exact hgate.1
  · rw [lpReplicaCurrentCopies_transportTag, hsources]
    exact hgate.2.1
  · rw [lpReplicaRowCopies_transportTag, hconn]
    exact hgate.2.2.1
  · rw [lpReplicaCurrentCopies_transportTag, hsources]
    exact hgate.2.2.2.1
  · rw [lpReplicaCurrentCopies_transportTag, hsources]
    exact hgate.2.2.2.2.1
  · rw [lpReplicaRowCopies_transportTag, hconn]
    exact hgate.2.2.2.2.2

end

end StatMech.Ising
