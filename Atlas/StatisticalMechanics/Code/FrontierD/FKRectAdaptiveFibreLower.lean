/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectCutPushforward
import Code.FrontierD.FKRectRandomClusterEventFKG
import Code.Probability.AdaptiveFibreLower



open scoped BigOperators

namespace StatMech.FrontierD

noncomputable section



theorem fkRectCriticalEventMass_adaptive_fibre_lower
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (P : R.Configuration -> R.Configuration)
    (hP : forall omega, P (P omega) = P omega)
    (Base Goal : Set R.Configuration)
    (Arm : R.Configuration -> Set R.Configuration) (c : Real)
    (hBase : forall {omega rho}, P omega = P rho ->
      (omega ∈ Base ↔ rho ∈ Base))
    (hglue : forall {omega}, omega ∈ Base ->
      omega ∈ Arm (P omega) -> omega ∈ Goal)
    (hfloor : forall psi, psi ∈ Finset.univ.image P ->
      c * (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          fkRectCriticalRandomClusterProb R q omega) <=
        ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          (Arm psi).indicator
            (fun omega => fkRectCriticalRandomClusterProb R q omega) omega) :
    c * fkRectCriticalEventMass R q Base <=
      fkRectCriticalEventMass R q Goal := by
  rw [fkRectCriticalEventMass, fkRectCriticalEventMass]
  exact StatMech.Probability.finiteEventMass_adaptive_fibre_lower
    (fun omega => fkRectCriticalRandomClusterProb R q omega)
    (fkRectCriticalRandomClusterProb_nonneg R hq)
    P hP Base Goal Arm c hBase hglue hfloor





theorem fkRectCritical_rsw_stopping_sixth_power
    (R : FKRectTorus) {q alpha c : Real} (hq : 1 <= q)
    (halpha : 0 <= alpha) (hc : 0 <= c)
    (E0 E1 Goal : Set R.Configuration)
    (hE0inc : IsIncreasing E0) (hE1inc : IsIncreasing E1)
    (hE0 : alpha ^ 3 / 4 <= fkRectCriticalEventMass R q E0)
    (hE1 : alpha ^ 3 / 4 <= fkRectCriticalEventMass R q E1)
    (P : R.Configuration -> R.Configuration)
    (hP : forall omega, P (P omega) = P omega)
    (Arm : R.Configuration -> Set R.Configuration)
    (hBase : forall {omega rho}, P omega = P rho ->
      (omega ∈ E0 ∩ E1 ↔ rho ∈ E0 ∩ E1))
    (hglue : forall {omega}, omega ∈ E0 ∩ E1 ->
      omega ∈ Arm (P omega) -> omega ∈ Goal)
    (hfloor : forall psi, psi ∈ Finset.univ.image P ->
      c * (∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          fkRectCriticalRandomClusterProb R q omega) <=
        ∑ omega ∈ (Finset.univ.filter fun omega => P omega = psi),
          (Arm psi).indicator
            (fun omega => fkRectCriticalRandomClusterProb R q omega) omega) :
    c * (alpha ^ 6 / 16) <= fkRectCriticalEventMass R q Goal := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hfkg : fkRectCriticalEventMass R q E0 *
        fkRectCriticalEventMass R q E1 <=
      fkRectCriticalEventMass R q (E0 ∩ E1) :=
    fkRectCriticalEventMass_mul_le_inter R hq hE0inc hE1inc
  have hdiag : (alpha ^ 3 / 4) * (alpha ^ 3 / 4) <=
      fkRectCriticalEventMass R q E0 * fkRectCriticalEventMass R q E1 := by
    exact mul_le_mul hE0 hE1 (by positivity)
      (fkRectCriticalEventMass_nonneg R hq0 E0)
  have hbase : alpha ^ 6 / 16 <=
      fkRectCriticalEventMass R q (E0 ∩ E1) := by
    calc
      alpha ^ 6 / 16 = (alpha ^ 3 / 4) * (alpha ^ 3 / 4) := by ring
      _ <= _ := hdiag
      _ <= _ := hfkg
  have hexplore := fkRectCriticalEventMass_adaptive_fibre_lower
    R hq0 P hP (E0 ∩ E1) Goal Arm c hBase hglue hfloor
  exact (mul_le_mul_of_nonneg_left hbase hc).trans hexplore

end

end StatMech.FrontierD
