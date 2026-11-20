/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.TorusPrimitiveResidue
import Code.FrontierD.FKRectBlackOrbitRibbonParityCapstone
import Code.FrontierD.FKRectVerticalWindingPrimitiveArithmetic



namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section



theorem fkRectBlackBoundaryPrimalCycleWinding_primitive
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hnonzero : fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d) ≠ (0, 0)) :
    FKRectPrimitiveWinding
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)) := by
  letI : Fact (2 < fkRectBlackOrbitRibbonSubdivisionSide R) :=
    ⟨fkRectBlackOrbitRibbonSubdivisionSide_gt_two R⟩
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  exact ons_simpleLoop_winding_primitive
    (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d)
    (fkRectBlackOrbitFaithfulRibbonSubdivisionDart_valid R omega d)
    (fkRectBlackOrbitFaithfulRibbonSubdivisionDart_site_injective R omega d)
    (fkRectBlackOrbitFaithfulRibbonSubdivisionDart_nonUturn R omega d)
    w.1 w.2
    (fkRectBlackOrbitFaithfulRibbonSubdivisionDart_exponentX_sum R omega d)
    (fkRectBlackOrbitFaithfulRibbonSubdivisionDart_exponentY_sum R omega d)
    hnonzero



theorem fkRectBlackBoundaryPrimalCycleWinding_primitive_of_snd_pos
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2) :
    FKRectPrimitiveWinding
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)) := by
  apply fkRectBlackBoundaryPrimalCycleWinding_primitive R omega d
  intro hzero
  have hsnd := congrArg Prod.snd hzero
  simp only at hsnd
  omega

end

end StatMech.FrontierD
