/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectSeamForcing
import Code.FrontierD.FKRectMedialLoopTurnClassification
import Code.FrontierD.FKRectRefinedIntersection









open Equiv Finset SimpleGraph

namespace StatMech.FrontierD

open FKMedialTurningFiber StatMech.Onsager

noncomputable section



def fkRectBlackBoundaryPrimalCycleWalk
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    (fkRectOpenGraph R omega).Walk
      (fkRectMedialDartPrimalLabel R d.1)
      (fkRectMedialDartPrimalLabel R d.1) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let n := (fkRectBlackOrbitList pairing d).length
  let p := fkRectMedialBoundaryPrimalTrace R omega d.1 n
  have hblack : (fkMedialBlackBoundaryPerm pairing)^[n] d = d := by
    exact fkRectBlackBoundaryPerm_pow_length_apply pairing d
  have hdart : (fkMedialBoundaryStep pairing)^[n] d.1 = d.1 := by
    rw [← fkMedialBlackBoundaryPerm_iterate_val pairing d n, hblack]
  exact p.copy rfl (congrArg (fkRectMedialDartPrimalLabel R) hdart)

theorem fkRectBlackBoundaryPrimalCycleWalk_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d) =
      fkRectMedialBoundaryPrimalSeamTrace R
        (fkRectConfigurationToMedialPairing R omega) d.1
        (fkRectBlackOrbitList
          (fkRectConfigurationToMedialPairing R omega) d).length := by
  unfold fkRectBlackBoundaryPrimalCycleWalk
  rw [fkRectWalkWinding_copy]
  exact fkRectMedialBoundaryPrimalTrace_winding R omega d.1 _



theorem fkRectBlackOrbitDisplacement_ne_zero_of_turn_eq_zero
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (C : FKMedialLoop R.medialTorus pairing)
    (d : FKMedialBlackDart R.medialTorus)
    (hdC : (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
      d.1 = C)
    (hturn : canonicalComponentTurn pairing C = 0) :
    ons_pathDisplacement
        (List.ofFn (fkRectBlackOrbitDirection pairing d)) ≠ (0, 0) := by
  intro hzero
  have hcontract :=
    fkRectBlackOrbit_contractible_cyclicTurnSum R pairing d hzero
  have hcanon := canonicalComponentTurn_eq_toList_sum pairing C d hdC
  have hcyc := cyclicTurnSum_toList_strandDirections pairing d
  have hturnsum :
      ons_cyclicTurnSum
          ((fkMedialBlackBoundaryPerm pairing).toList d |>.map
            (fun e : FKMedialBlackDart R.medialTorus =>
              fkMedialStrandDirection pairing e.1)) = 0 := by
    rw [hcyc, ← hcanon, hturn]
    norm_num
  rw [← fkRectBlackOrbitList, ← fkRectBlackOrbitDirection_ofFn] at hturnsum
  rcases hcontract with hfour | hnegfour <;> omega



theorem fkRectBlackBoundaryPrimalCycleWalk_winding_ne_zero_of_displacement
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hdisp : ons_pathDisplacement
      (List.ofFn (fkRectBlackOrbitDirection
        (fkRectConfigurationToMedialPairing R omega) d)) ≠ (0, 0)) :
    fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d) ≠ (0, 0) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let n := (fkRectBlackOrbitList pairing d).length
  let D := ons_pathDisplacement
    (List.ofFn (fkRectBlackOrbitDirection pairing d))
  intro hwind
  have htrace : fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 n =
      (0, 0) := by
    simpa [pairing, n] using
      (fkRectBlackBoundaryPrimalCycleWalk_winding R omega d).symm.trans hwind
  have hblack : (fkMedialBlackBoundaryPerm pairing)^[n] d = d := by
    exact fkRectBlackBoundaryPerm_pow_length_apply pairing d
  have hdart : (fkMedialBoundaryStep pairing)^[n] d.1 = d.1 := by
    rw [← fkMedialBlackBoundaryPerm_iterate_val pairing d n, hblack]
  have hcenter := fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck
    R pairing d.1 (0, 0) n
  rw [hdart, htrace] at hcenter
  simp only [fkRectSquareDeckTranslation, mul_zero, add_zero,
    add_sub_cancel_right] at hcenter
  norm_num at hcenter
  have hpointZero :
      fkRectBlackBoundaryPointAfter R pairing d n =
        fkRectBlackBoundaryPointAfter R pairing d 0 := by
    unfold fkRectBlackBoundaryPointAfter
    rw [hblack]
    simp only [fkRectRefinedBoundaryCenterAfter]
    rw [hcenter]
    simp only [Function.iterate_zero_apply]
  have hpointD := fkRectBlackBoundaryPointAfter_eq_prefix
    R pairing d n
  have hprefix := fkRectBlackOrbitPrefix_length_eq_displacement pairing d
  change fkRectBlackOrbitPrefix pairing d n = D at hprefix
  rw [hprefix] at hpointD
  rw [hpointZero] at hpointD
  have hD : D = (0, 0) := by
    have hsmul : 2 • D = 0 := by
      exact left_eq_add.mp hpointD
    exact two_nsmul_eq_zero.mp hsmul
  exact hdisp (by simpa [pairing, D] using hD)



theorem exists_nonzero_primalBoundaryWinding_of_zeroTurn
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))
    (hturn : canonicalComponentTurn
      (fkRectConfigurationToMedialPairing R omega) C = 0) :
    ∃ d : FKMedialBlackDart R.medialTorus,
      (fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          d.1 = C ∧
        fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d) ≠ (0, 0) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  obtain ⟨A, hA⟩ :=
    (fkMedialBlackBoundaryCycleToLoop_bijective pairing).2 C
  induction A using Quot.ind with
  | _ d =>
      change (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
        d.1 = C at hA
      refine ⟨d, hA, ?_⟩
      apply fkRectBlackBoundaryPrimalCycleWalk_winding_ne_zero_of_displacement
      exact fkRectBlackOrbitDisplacement_ne_zero_of_turn_eq_zero
        R pairing C d hA hturn

end

end StatMech.FrontierD
