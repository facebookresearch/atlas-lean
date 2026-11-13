/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching











open Finset

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaPairedCutHallExactDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

local instance lpReplicaPairedCutHallExactTargetDecidableEq
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    DecidableEq (LPReplicaOffdiagDecoratedTarget G sites i j q) :=
  Classical.decEq _



theorem lpReplicaOffdiagCoupledPairedNeighbors_eq_outputs
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    lpReplicaOffdiagCoupledPairedNeighbors G sites i j q z =
      lpReplicaOffdiagCoupledPairedOutputs G sites i j q := by
  ext y
  simp only [lpReplicaOffdiagCoupledPairedNeighbors,
    lpReplicaOffdiagCoupledPairedOutputs, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact lpReplicaOffdiagCoupledPairedMatch_iff_output G sites i j q z y


theorem lpReplicaOffdiagCoupledPairedNeighbors_card
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    (lpReplicaOffdiagCoupledPairedNeighbors G sites i j q z).card =
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card := by
  rw [lpReplicaOffdiagCoupledPairedNeighbors_eq_outputs]



theorem lpReplicaOffdiagCoupledPaired_biUnion_eq_outputs_of_nonempty
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (LPReplicaOffdiagDecoratedSource G sites i j q))
    (hS : S.Nonempty) :
    S.biUnion (lpReplicaOffdiagCoupledPairedNeighbors G sites i j q) =
      lpReplicaOffdiagCoupledPairedOutputs G sites i j q := by
  classical
  ext y
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨z, hz, hy⟩
    rwa [lpReplicaOffdiagCoupledPairedNeighbors_eq_outputs
      G sites i j q z] at hy
  · intro hy
    obtain ⟨z, hz⟩ := hS
    exact ⟨z, hz, by
      rwa [lpReplicaOffdiagCoupledPairedNeighbors_eq_outputs
        G sites i j q z]⟩



theorem lpReplicaOffdiagCoupledPairedHall_iff_outputCard
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOffdiagCoupledPairedHall G sites i j q ↔
      Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
        (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card := by
  constructor
  · intro hHall
    classical
    dsimp only [LPReplicaOffdiagCoupledPairedHall] at hHall
    by_cases hU : (Finset.univ : Finset
        (LPReplicaOffdiagDecoratedSource G sites i j q)).Nonempty
    · have h := hHall (Finset.univ : Finset
          (LPReplicaOffdiagDecoratedSource G sites i j q))
      calc
        Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) =
            (Finset.univ : Finset
              (LPReplicaOffdiagDecoratedSource G sites i j q)).card := by
              rw [Finset.card_univ]
        _ <= ((Finset.univ : Finset
              (LPReplicaOffdiagDecoratedSource G sites i j q)).biUnion
                (lpReplicaOffdiagCoupledPairedNeighbors
                  G sites i j q)).card := by
          convert h using 1
          congr 1
          ext y
          simp only [Finset.mem_biUnion]
        _ = (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card :=
          congrArg Finset.card
            (lpReplicaOffdiagCoupledPaired_biUnion_eq_outputs_of_nonempty
              G sites i j q Finset.univ hU)
    · have hEmpty : (Finset.univ : Finset
          (LPReplicaOffdiagDecoratedSource G sites i j q)) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hU
      have hzero : Fintype.card
          (LPReplicaOffdiagDecoratedSource G sites i j q) = 0 := by
        rw [← Finset.card_univ, hEmpty]
        rfl
      rw [hzero]
      exact Nat.zero_le _
  · exact lpReplicaOffdiagCoupledPairedHall_of_outputCard G sites i j q

end

end StatMech.Ising
