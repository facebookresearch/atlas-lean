/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryVerticalFlux
import Code.FrontierD.FKRectPrimalBoundaryFiberWinding










namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 800000 in



theorem fkMedialLoopCanonicalVerticalFlux_blackBoundaryCycleToLoop
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectConfigurationBlackBoundaryCycle R omega) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    fkMedialLoopCanonicalVerticalFlux pairing
        (fkMedialBlackBoundaryCycleToLoop pairing C) =
      -(fkRectBlackBoundaryCycleWinding R omega C).2 := by
  induction C using Quot.ind with
  | _ d =>
    simp only [fkRectBlackBoundaryCycleWinding_mk]
    change fkMedialLoopCanonicalVerticalFlux
        (fkRectConfigurationToMedialPairing R omega)
          ((fkMedialLoopGraph R.medialTorus
            (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
              d.1) =
      -(fkRectBlackBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R omega) d).2
    rw [← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass]
    exact fkMedialLoopCanonicalVerticalFlux_eq_neg_blackBoundaryWinding
      R omega d


theorem fkRectUnorientedVerticalWindingTotal_eq_sum_blackBoundaryCycle
    (R : FKRectTorus) (omega : R.Configuration) :
    fkMedialUnorientedVerticalWindingTotal
        (fkRectConfigurationToMedialPairing R omega) =
      ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
        (fkRectBlackBoundaryCycleWinding R omega C).2.natAbs := by
  classical
  let pairing := fkRectConfigurationToMedialPairing R omega
  let e : FKRectConfigurationBlackBoundaryCycle R omega ≃
      FKMedialLoop R.medialTorus pairing :=
    Equiv.ofBijective (fkMedialBlackBoundaryCycleToLoop pairing)
      (fkMedialBlackBoundaryCycleToLoop_bijective pairing)
  unfold fkMedialUnorientedVerticalWindingTotal
  symm
  apply Fintype.sum_equiv e
  intro C
  change (fkRectBlackBoundaryCycleWinding R omega C).2.natAbs =
    (fkMedialLoopCanonicalVerticalFlux pairing (e C)).natAbs
  have hflux :=
    fkMedialLoopCanonicalVerticalFlux_blackBoundaryCycleToLoop R omega C
  change fkMedialLoopCanonicalVerticalFlux pairing
      (fkMedialBlackBoundaryCycleToLoop pairing C) =
    -(fkRectBlackBoundaryCycleWinding R omega C).2 at hflux
  have he : e C = fkMedialBlackBoundaryCycleToLoop pairing C := rfl
  rw [he, hflux, Int.natAbs_neg]

end

end StatMech.FrontierD
