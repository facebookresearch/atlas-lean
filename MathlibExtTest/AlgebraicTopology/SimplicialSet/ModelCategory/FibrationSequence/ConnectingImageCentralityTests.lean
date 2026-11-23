/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.ConnectingImageCentrality
import Batteries.Tactic.Lint

/-!
# Clients of original connecting-image centrality

The original based-path sequence and its original loop shift recover
commutation in the fundamental group of the strict loop space. This
checks the positive-degree indices and the selected original loop point.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory
open scoped Simplicial SSet.modelCategoryQuillen

namespace MathlibExtTest.ConnectingImageCentrality

open SSet.FibrationSequence.Geometry
open SSet.LoopShiftOriginalGeometry (originalLoopPoint loopConnectingEquiv)

#check @sequenceConnectingGroupHom_range_le_center
#print axioms sequenceConnectingGroupHom_range_le_center
#print axioms SSet.KanComplex.map_mem_center_of_product_unit
#print axioms SSet.KanComplex.commute_of_product_projections_eq_one
#print axioms fiberLoopAction_unit

example (X : SSet.{u}) [SSet.KanComplex X] (x : X _⦋0⦌)
    (a b : SSet.KanComplex.π 1 (SSet.loopSpace X x) (originalLoopPoint X x)) :
    Commute a b := by
  let S := SSet.loopFibrationSequence X x
  obtain ⟨q, hq⟩ := (loopConnectingEquiv 1 X x).surjective b
  have hb : b ∈ (sequenceConnectingGroupHom S 0).range := by
    refine ⟨q, ?_⟩
    change S.connectingMap 1 q = b
    exact hq
  exact (Subgroup.mem_center_iff.mp (sequenceConnectingGroupHom_range_le_center S hb)) a

#lint only unusedArguments in
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.ConnectingImageCentrality

end MathlibExtTest.ConnectingImageCentrality
