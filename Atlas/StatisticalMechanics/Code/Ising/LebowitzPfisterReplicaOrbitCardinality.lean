/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitGateFamily









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



theorem lpReplicaRowFiberMass_eq_cardinalSum
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaRowFiberMass G sites beta J hf r A B m =
      ∑ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m},
        (#(lpReplicaDisconnProfileFamily G sites A K.1) : Real) *
          (#(lpReplicaDisconnProfileFamily G sites B
            (lpReplicaReflectedResidual G sites m K.1)) : Real) *
          (weight (lpReplicaCurrentGraph G sites) beta
              (lpReplicaCurrentCoupling J hf r)
              (ofEdgeFun (lpReplicaCurrentGraph G sites) K.1) *
            weight (lpReplicaCurrentGraph G sites) beta
              (lpReplicaCurrentCoupling J hf r)
              (ofEdgeFun (lpReplicaCurrentGraph G sites)
                (lpReplicaReflectedResidual G sites m K.1))) := by
  unfold lpReplicaRowFiberMass
  apply Finset.sum_congr rfl
  intro K _
  rw [lpReplicaDisconnProfileTerm_eq_card_mul_weight,
    lpReplicaDisconnProfileTerm_eq_card_mul_weight]
  ring



theorem lpReplicaProfileOrbitMass_eq_cardinalSum
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaProfileOrbitMass G sites beta J hf r A B q =
      ∑ m : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
          lpReplicaSymmetrizedProfile G sites p = q},
        ∑ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
            a <= m.1},
          (#(lpReplicaDisconnProfileFamily G sites A K.1) : Real) *
            (#(lpReplicaDisconnProfileFamily G sites B
              (lpReplicaReflectedResidual G sites m.1 K.1)) : Real) *
            (weight (lpReplicaCurrentGraph G sites) beta
                (lpReplicaCurrentCoupling J hf r)
                (ofEdgeFun (lpReplicaCurrentGraph G sites) K.1) *
              weight (lpReplicaCurrentGraph G sites) beta
                (lpReplicaCurrentCoupling J hf r)
                (ofEdgeFun (lpReplicaCurrentGraph G sites)
                  (lpReplicaReflectedResidual G sites m.1 K.1))) := by
  rw [lpReplicaProfileOrbitMass_eq_sum]
  apply Finset.sum_congr rfl
  intro m _
  exact lpReplicaRowFiberMass_eq_cardinalSum
    G sites beta J hf r A B m.1



def LPReplicaOrbitConfiguration
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Σ m : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites p = q},
    Σ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
        a <= m.1},
      (↑(lpReplicaDisconnProfileFamily G sites A K.1) ×
        ↑(lpReplicaDisconnProfileFamily G sites B
          (lpReplicaReflectedResidual G sites m.1 K.1)))

noncomputable instance instFintypeLPReplicaOrbitConfiguration
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaOrbitConfiguration G sites A B q) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  letI : Fintype {p : H.edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites p = q} :=
    lpReplicaProfileOrbitFintype G sites q
  letI (m : {p : H.edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites p = q}) :
      Fintype {a : H.edgeFinset -> Nat // a <= m.1} :=
    StatMech.Sharpness.instFintypeLe H m.1
  unfold LPReplicaOrbitConfiguration
  infer_instance



def lpReplicaOrbitConfigurationWeight
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (x : LPReplicaOrbitConfiguration G sites A B q) : Real :=
  weight (lpReplicaCurrentGraph G sites) beta
      (lpReplicaCurrentCoupling J hf r)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) x.2.1.1) *
    weight (lpReplicaCurrentGraph G sites) beta
      (lpReplicaCurrentCoupling J hf r)
      (ofEdgeFun (lpReplicaCurrentGraph G sites)
        (lpReplicaReflectedResidual G sites x.1.1 x.2.1.1))


theorem lpReplicaProfileOrbitMass_eq_sum_configurationWeight
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaProfileOrbitMass G sites beta J hf r A B q =
      ∑ x : LPReplicaOrbitConfiguration G sites A B q,
        lpReplicaOrbitConfigurationWeight
          G sites beta J hf r A B q x := by
  classical
  rw [lpReplicaProfileOrbitMass_eq_cardinalSum]
  change _ = ∑ x : (Σ m : _, Σ K : _, _),
    lpReplicaOrbitConfigurationWeight
      G sites beta J hf r A B q x
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro m _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro K _
  simp only [lpReplicaOrbitConfigurationWeight, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
    Fintype.card_coe, Nat.cast_mul]



theorem lpReplicaProfileOrbitMass_le_add_of_weightedInjection
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B C D E F : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (move : LPReplicaOrbitConfiguration G sites A B q ->
      LPReplicaOrbitConfiguration G sites C D q ⊕
        LPReplicaOrbitConfiguration G sites E F q)
    (hmove : Function.Injective move)
    (hweight : ∀ x,
      lpReplicaOrbitConfigurationWeight G sites beta J hf r A B q x =
        match move x with
        | .inl y => lpReplicaOrbitConfigurationWeight
            G sites beta J hf r C D q y
        | .inr y => lpReplicaOrbitConfigurationWeight
            G sites beta J hf r E F q y) :
    lpReplicaProfileOrbitMass G sites beta J hf r A B q <=
      lpReplicaProfileOrbitMass G sites beta J hf r C D q +
        lpReplicaProfileOrbitMass G sites beta J hf r E F q := by
  classical
  let X := LPReplicaOrbitConfiguration G sites A B q
  let Y1 := LPReplicaOrbitConfiguration G sites C D q
  let Y2 := LPReplicaOrbitConfiguration G sites E F q
  let wX : X -> Real := lpReplicaOrbitConfigurationWeight
    G sites beta J hf r A B q
  let wY : Y1 ⊕ Y2 -> Real
    | .inl y => lpReplicaOrbitConfigurationWeight
        G sites beta J hf r C D q y
    | .inr y => lpReplicaOrbitConfigurationWeight
        G sites beta J hf r E F q y
  rw [lpReplicaProfileOrbitMass_eq_sum_configurationWeight,
    lpReplicaProfileOrbitMass_eq_sum_configurationWeight,
    lpReplicaProfileOrbitMass_eq_sum_configurationWeight]
  change (∑ x : X, wX x) <=
    (∑ y : Y1, wY (.inl y)) + ∑ y : Y2, wY (.inr y)
  rw [<- Fintype.sum_sum_type wY]
  have himage : (∑ y ∈ Finset.univ.image move, wY y) =
      ∑ x : X, wX x := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro x _
      dsimp only [wX, wY]
      rcases hx : move x with y | y
      · simpa only [hx] using (hweight x).symm
      · simpa only [hx] using (hweight x).symm
    · intro x _ y _ hxy
      exact hmove hxy
  rw [<- himage]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.subset_univ _
  · intro y _ _
    rcases y with y | y
    · exact mul_nonneg
        (StatMech.Ising.acw_weight_nonneg
          (lpReplicaCurrentGraph G sites) beta
          (lpReplicaCurrentCoupling J hf r) hbeta
          (lpReplicaCurrentCoupling_nonneg J hf r hJ hhf hr) _)
        (StatMech.Ising.acw_weight_nonneg
          (lpReplicaCurrentGraph G sites) beta
          (lpReplicaCurrentCoupling J hf r) hbeta
          (lpReplicaCurrentCoupling_nonneg J hf r hJ hhf hr) _)
    · exact mul_nonneg
        (StatMech.Ising.acw_weight_nonneg
          (lpReplicaCurrentGraph G sites) beta
          (lpReplicaCurrentCoupling J hf r) hbeta
          (lpReplicaCurrentCoupling_nonneg J hf r hJ hhf hr) _)
        (StatMech.Ising.acw_weight_nonneg
          (lpReplicaCurrentGraph G sites) beta
          (lpReplicaCurrentCoupling J hf r) hbeta
          (lpReplicaCurrentCoupling_nonneg J hf r hJ hhf hr) _)

end

end StatMech.Ising
