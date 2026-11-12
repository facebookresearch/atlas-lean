/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitAtoms









open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



theorem lpReplicaCollisionSplitMultiplicity_eq_edgeProduct
    (G : SimpleGraph V) (sites : I -> V)
    (m K : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaCollisionSplitMultiplicity G sites m K =
      ∏ e : (lpReplicaCurrentGraph G sites).edgeFinset,
        Nat.choose (m e) (K e) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  unfold lpReplicaCollisionSplitMultiplicity
  rw [<- Finset.prod_attach H.edgeFinset]
  apply Finset.prod_congr rfl
  intro e he
  simp only [ofEdgeFun]
  rw [dif_pos e.2, dif_pos e.2]


def LPReplicaCollisionSplitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (m K : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  ↑((Finset.univ : Finset
      (Finset (Copy (lpReplicaCurrentGraph G sites) m))).filter fun S =>
        profileFlux (lpReplicaCurrentGraph G sites) m S = K)

noncomputable instance instFintypeLPReplicaCollisionSplitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (m K : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaCollisionSplitLabel G sites m K) := by
  classical
  unfold LPReplicaCollisionSplitLabel
  infer_instance

theorem card_lpReplicaCollisionSplitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (m K : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaCollisionSplitLabel G sites m K) =
      lpReplicaCollisionSplitMultiplicity G sites m K := by
  classical
  unfold LPReplicaCollisionSplitLabel
  rw [Fintype.card_coe,
    preimage_count (lpReplicaCurrentGraph G sites) m K]
  exact (lpReplicaCollisionSplitMultiplicity_eq_edgeProduct
    G sites m K).symm



def LPReplicaProfileOrbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  ∀ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
    ↑((Finset.univ : Finset (Fin (q e.1))).powersetCard (m e.1))

noncomputable instance instFintypeLPReplicaProfileOrbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaProfileOrbitLabel G sites q m) := by
  classical
  unfold LPReplicaProfileOrbitLabel
  infer_instance

theorem card_lpReplicaProfileOrbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaProfileOrbitLabel G sites q m) =
      lpReplicaProfileOrbitMultiplicity G sites q m := by
  classical
  unfold LPReplicaProfileOrbitLabel lpReplicaProfileOrbitMultiplicity
  calc
    _ = ∏ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
        Fintype.card
          ↑((Finset.univ : Finset (Fin (q e.1))).powersetCard (m e.1)) :=
      Fintype.card_pi
    _ = _ := by
      rw [<- Finset.prod_attach
        (lpReplicaCurrentEdgeOrbitStrictReps G sites)]
      apply Finset.prod_congr rfl
      intro e he
      rw [Fintype.card_coe, Finset.card_powersetCard]
      simp



def LPReplicaDecoratedOrbitAtom
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Σ x : LPReplicaOrbitConfiguration G sites A B q,
    LPReplicaCollisionSplitLabel G sites x.1.1 x.2.1.1 ×
      LPReplicaProfileOrbitLabel G sites q x.1.1

noncomputable instance instFintypeLPReplicaDecoratedOrbitAtom
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaDecoratedOrbitAtom G sites A B q) := by
  classical
  unfold LPReplicaDecoratedOrbitAtom
  infer_instance



theorem card_lpReplicaDecoratedOrbitAtom
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaDecoratedOrbitAtom G sites A B q) =
      Fintype.card (LPReplicaOrbitAtom G sites A B q) := by
  classical
  rw [card_lpReplicaOrbitAtom]
  unfold LPReplicaDecoratedOrbitAtom
  change Fintype.card
      (Σ x : LPReplicaOrbitConfiguration G sites A B q,
        LPReplicaCollisionSplitLabel G sites x.1.1 x.2.1.1 ×
          LPReplicaProfileOrbitLabel G sites q x.1.1) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.card_prod,
    card_lpReplicaCollisionSplitLabel,
    card_lpReplicaProfileOrbitLabel]
  rfl



def LPReplicaOffdiagDecoratedOrbitInjection
    (G : SimpleGraph V) (sites : I -> V)
    (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop :=
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  ∃ move : LPReplicaDecoratedOrbitAtom G sites ∅ (Si ∆ Sj ∆ T) q ->
      LPReplicaDecoratedOrbitAtom G sites Si (Sj ∆ T) q ⊕
        LPReplicaDecoratedOrbitAtom G sites Sj (Si ∆ T) q,
    Function.Injective move


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_decoratedInjection
    (G : SimpleGraph V) (sites : I -> V)
    (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hinj : LPReplicaOffdiagDecoratedOrbitInjection G sites i j q) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  obtain ⟨move, hmove⟩ := hinj
  dsimp only [LPReplicaOffdiagOrbitAtomCardInequality,
    LPReplicaOffdiagDecoratedOrbitInjection] at ⊢
  rw [<- card_lpReplicaDecoratedOrbitAtom,
    <- card_lpReplicaDecoratedOrbitAtom,
    <- card_lpReplicaDecoratedOrbitAtom,
    <- Fintype.card_sum]
  exact Fintype.card_le_of_injective move hmove



theorem lpReplicaAggregateProfileOrbitInequality_of_decoratedInjections
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hinj : ∀ q i j, i ≠ j ->
      LPReplicaOffdiagDecoratedOrbitInjection G sites i j q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_atomCard
    G sites beta J hf r hbeta hJ hhf hr
  intro q i j hij
  exact lpReplicaOffdiagOrbitAtomCardInequality_of_decoratedInjection
    G sites i j q (hinj q i j hij)

end

end StatMech.Ising
