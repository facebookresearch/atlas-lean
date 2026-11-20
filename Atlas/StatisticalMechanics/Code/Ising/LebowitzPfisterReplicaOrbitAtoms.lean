/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitWeight









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


noncomputable def lpReplicaCollisionSplitMultiplicity
    (G : SimpleGraph V) (sites : I -> V)
    (m K : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Nat :=
  ∏ e ∈ (lpReplicaCurrentGraph G sites).edgeFinset,
    Nat.choose
      ((ofEdgeFun (lpReplicaCurrentGraph G sites) m) e)
      ((ofEdgeFun (lpReplicaCurrentGraph G sites) K) e)


noncomputable def lpReplicaOrbitConfigurationMultiplicity
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (x : LPReplicaOrbitConfiguration G sites A B q) : Nat :=
  lpReplicaCollisionSplitMultiplicity G sites x.1.1 x.2.1.1 *
    lpReplicaProfileOrbitMultiplicity G sites q x.1.1



theorem lpReplicaOrbitConfigurationWeight_eq_multiplicity_mul_base
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (x : LPReplicaOrbitConfiguration G sites A B q) :
    lpReplicaOrbitConfigurationWeight G sites beta J hf r A B q x =
      (lpReplicaOrbitConfigurationMultiplicity G sites A B q x : Real) *
        lpReplicaProfileOrbitBaseWeight G sites beta J hf r q := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  let m := x.1.1
  let K := x.2.1.1
  have hsplit := weight_split_eq_binom H beta Jr m K x.2.1.2
  unfold lpReplicaOrbitConfigurationWeight
  rw [lpReplicaReflectedResidual_weight]
  change weight H beta Jr (ofEdgeFun H K) *
      weight H beta Jr (ofEdgeFun H (fun e => m e - K e)) = _
  rw [hsplit]
  rw [lpReplicaWeight_eq_orbitMultiplicity_mul_base
    G sites beta J hf r q m x.1.2]
  unfold lpReplicaOrbitConfigurationMultiplicity
  unfold lpReplicaCollisionSplitMultiplicity
  rw [Nat.cast_mul, Nat.cast_prod]
  ring



def LPReplicaOrbitAtom
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Σ x : LPReplicaOrbitConfiguration G sites A B q,
    Fin (lpReplicaOrbitConfigurationMultiplicity G sites A B q x)

noncomputable instance instFintypeLPReplicaOrbitAtom
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaOrbitAtom G sites A B q) := by
  classical
  unfold LPReplicaOrbitAtom
  infer_instance



theorem card_lpReplicaOrbitAtom
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOrbitAtom G sites A B q) =
      ∑ x : LPReplicaOrbitConfiguration G sites A B q,
        lpReplicaOrbitConfigurationMultiplicity G sites A B q x := by
  classical
  unfold LPReplicaOrbitAtom
  change Fintype.card
      (Σ x : LPReplicaOrbitConfiguration G sites A B q,
        Fin (lpReplicaOrbitConfigurationMultiplicity G sites A B q x)) = _
  calc
    _ = ∑ x : LPReplicaOrbitConfiguration G sites A B q,
        Fintype.card
          (Fin (lpReplicaOrbitConfigurationMultiplicity G sites A B q x)) :=
      Fintype.card_sigma
    _ = _ := by simp



theorem lpReplicaProfileOrbitMass_eq_card_atoms_mul_base
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaProfileOrbitMass G sites beta J hf r A B q =
      (Fintype.card (LPReplicaOrbitAtom G sites A B q) : Real) *
        lpReplicaProfileOrbitBaseWeight G sites beta J hf r q := by
  classical
  rw [lpReplicaProfileOrbitMass_eq_sum_configurationWeight]
  simp_rw [lpReplicaOrbitConfigurationWeight_eq_multiplicity_mul_base]
  rw [<- Finset.sum_mul]
  rw [<- Nat.cast_sum]
  rw [<- card_lpReplicaOrbitAtom G sites A B q]



theorem lpReplicaProfileOrbitBaseWeight_nonneg
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    0 <= lpReplicaProfileOrbitBaseWeight G sites beta J hf r q := by
  classical
  unfold lpReplicaProfileOrbitBaseWeight
  apply mul_nonneg <;> apply Finset.prod_nonneg <;> intro e _
  · exact div_nonneg
      (pow_nonneg (mul_nonneg hbeta
        (lpReplicaCurrentCoupling_nonneg J hf r hJ hhf hr e.1)) _)
      (by positivity)
  · exact div_nonneg
      (pow_nonneg (mul_nonneg hbeta
        (lpReplicaCurrentCoupling_nonneg J hf r hJ hhf hr e.1)) _)
      (by positivity)



theorem lpReplicaProfileOrbitMass_le_add_of_card_atoms
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B C D E F : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitAtom G sites A B q) <=
      Fintype.card (LPReplicaOrbitAtom G sites C D q) +
        Fintype.card (LPReplicaOrbitAtom G sites E F q)) :
    lpReplicaProfileOrbitMass G sites beta J hf r A B q <=
      lpReplicaProfileOrbitMass G sites beta J hf r C D q +
        lpReplicaProfileOrbitMass G sites beta J hf r E F q := by
  rw [lpReplicaProfileOrbitMass_eq_card_atoms_mul_base,
    lpReplicaProfileOrbitMass_eq_card_atoms_mul_base,
    lpReplicaProfileOrbitMass_eq_card_atoms_mul_base]
  have hcardReal :
      (Fintype.card (LPReplicaOrbitAtom G sites A B q) : Real) <=
        Fintype.card (LPReplicaOrbitAtom G sites C D q) +
          Fintype.card (LPReplicaOrbitAtom G sites E F q) := by
    exact_mod_cast hcard
  have hbase := lpReplicaProfileOrbitBaseWeight_nonneg
    G sites beta J hf r hbeta hJ hhf hr q
  nlinarith only [mul_le_mul_of_nonneg_right hcardReal hbase]



def LPReplicaOffdiagOrbitAtomCardInequality
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
  Fintype.card (LPReplicaOrbitAtom G sites ∅ (Si ∆ Sj ∆ T) q) <=
    Fintype.card (LPReplicaOrbitAtom G sites Si (Sj ∆ T) q) +
      Fintype.card (LPReplicaOrbitAtom G sites Sj (Si ∆ T) q)



theorem lpReplicaAggregateProfileOrbitInequality_of_atomCard
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hcard : ∀ q i j, i ≠ j ->
      LPReplicaOffdiagOrbitAtomCardInequality G sites i j q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_offdiag
    G sites beta J hf r hbeta hJ hhf hr
  intro q i j hij
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  exact lpReplicaProfileOrbitMass_le_add_of_card_atoms
    G sites beta J hf r hbeta hJ hhf hr
      ∅ (Si ∆ Sj ∆ T) Si (Sj ∆ T) Sj (Si ∆ T) q
      (hcard q i j hij)

end

end StatMech.Ising
