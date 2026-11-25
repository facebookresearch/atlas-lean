/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialObject.LeftDecalage

/-!
# All original simplex generators of the one-sided decalage

The original ordinal sum retains the distinguished first vertex and
shifts every original face and degeneracy by one. The right-block
projection is the original first face, and the augmentation is the
original first vertex. All formulas are equalities of whole ordinal maps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.LeftDecalage

set_option backward.isDefEq.respectTransparency false in
/-- Every original face skips its same original vertex after the distinguished first vertex. -/
theorem ordinal_delta {n : ℕ} (i : Fin (n + 2)) :
    ordinal.map (SimplexCategory.δ i) = SimplexCategory.δ i.succ := by
  ext x
  refine Fin.cases ?_ (fun j => ?_) x
  · exact congrArg Fin.val (Fin.succ_succAbove_zero i).symm
  · exact congrArg Fin.val (Fin.succ_succAbove_succ i j).symm

set_option backward.isDefEq.respectTransparency false in
/-- Every original degeneracy duplicates its same original vertex after the distinguished first
vertex. -/
theorem ordinal_sigma {n : ℕ} (i : Fin (n + 1)) :
    ordinal.map (SimplexCategory.σ i) = SimplexCategory.σ i.succ := by
  ext x
  refine Fin.cases ?_ (fun j => ?_) x
  · exact congrArg Fin.val (Fin.predAbove_right_zero (i := i.succ)).symm
  · exact congrArg Fin.val (Fin.succ_predAbove_succ i j).symm

set_option backward.isDefEq.respectTransparency false in
/-- The original whole right-block inclusion is precisely the first original face. -/
theorem rightBlock_delta (n : ℕ) :
    rightBlock.app (SimplexCategory.mk n) = SimplexCategory.δ (0 : Fin (n + 2)) := by
  ext x
  rfl

end CategoryTheory.SimplicialObject.LeftDecalage
