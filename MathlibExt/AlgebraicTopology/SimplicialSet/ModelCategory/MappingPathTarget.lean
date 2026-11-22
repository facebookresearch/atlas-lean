/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetDeformationRetract

/-!
# The original mapping-path target and section equation

The original target evaluates the whole original path at its final
endpoint. Both this projection and its original section equation use
the mapping-path primitives for arbitrary simplicial sets.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory

namespace SSet

/-- The target map of the mapping path space: project to the path, then
evaluate at the far (`1`) endpoint. -/
noncomputable def mappingPathTarget {X B : SSet.{u}} (f : X ⟶ B) :
    mappingPathSpace (f := f) ⟶ B :=
  mappingPathEval f ≫ eval₁

/-- The mapping path space factors `f` as section followed by target. -/
theorem mappingPathSection_comp_target {X B : SSet.{u}} (f : X ⟶ B) :
    mappingPathSection f ≫ mappingPathTarget f = f := by
  unfold mappingPathTarget
  rw [← Category.assoc, mappingPathSection_comp_eval, Category.assoc,
    eval₁_constPath, Category.comp_id]

end SSet
