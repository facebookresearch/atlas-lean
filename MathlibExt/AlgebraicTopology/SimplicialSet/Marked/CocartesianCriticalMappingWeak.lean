/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CriticalParameterCorner
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterArrowComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterTerminalComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeTargetNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianWeakEquivalences
import Mathlib.CategoryTheory.LiftingProperties.Over

/-!
# Actual mapping weakness of the original cocartesian critical cells

Each original whole critical simplex may have any supplied marked map
to the maximally marked base. Its full scalar boundary corner retains
that base map and lifts against the intrinsic cocartesian projection.
The original mapping restrictions therefore have all boundary lifts and
are weak. The selected critical first edge, all marks and the original
non-Kan quasicategory base are retained.
-/

noncomputable section
universe u
open CategoryTheory Limits
open scoped Simplicial

namespace SSet.Marked

/-- The original marked critical cell lies over its supplied whole original target-to-base map. -/
def cocartesianCriticalOver {B : SSet.{u}} (m : ℕ) (r : cocartesianCriticalTarget.{u} m ⟶ max B) :
    Over.mk (cocartesianCriticalCell.{u} m ≫ r) ⟶ Over.mk r :=
  Over.homMk (cocartesianCriticalCell.{u} m) rfl

/-- Every full boundary-parameter square of the original critical slice cell lifts against the actual
  canonical cocartesian projection. -/
theorem cocartesianCriticalOver_boundary_lifting {B E : SSet.{u}} [Quasicategory B]
    (m n : ℕ) (r : cocartesianCriticalTarget.{u} m ⟶ max B)
    (p : E ⟶ B) [InnerFibration p] :
    HasLiftingProperty (overParameterPushoutProduct (boundary.{u} n).ι (cocartesianCriticalOver m r))
      (Over.mkIdTerminal.from (Over.mk (cocartesianProjection p))) := by
  let f := cocartesianCriticalOver m r
  let t := Over.mkIdTerminal.from (Over.mk (cocartesianProjection p))
  have ht : t.left = cocartesianProjection p := Over.mkIdTerminal_from_left _
  let _ : HasLiftingProperty
      (parameterPushoutProduct (boundary.{u} n).ι f.left) t.left :=
    ht.symm ▸ cocartesianCriticalParameter_boundary_lifting m n p
  let _ : HasLiftingProperty (overParameterPushoutProduct (boundary.{u} n).ι f).left t.left :=
    (HasLiftingProperty.iff_of_arrow_iso_left (overParameterMarkedArrowIso _ f) t.left).mpr inferInstance
  exact HasLiftingProperty.over _ t

/-- The original critical cell restriction has the full native mapping boundary-right property into every
  intrinsic cocartesian target. -/
theorem cocartesianCriticalOver_mapping_rlp {B : SSet.{u}} [Quasicategory B]
    (m : ℕ) (r : cocartesianCriticalTarget.{u} m ⟶ max B) (Y : CocartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp
      ((overMappingFunctor .maximal (max B) Y.obj).map (cocartesianCriticalOver m r).op) := by
  let p : Y.obj.left.toSSet ⟶ B := Y.obj.hom.hom
  let _ : CocartesianFibration p := Y.property.1
  let e : Y.obj ≅ Over.mk (cocartesianProjection p) :=
    Over.isoMk (cocartesianMarkingIso p Y.property.2) (Hom.ext rfl)
  have h : modelCategoryQuillen.I.{u}.rlp
      ((overMappingFunctor .maximal (max B) (Over.mk (cocartesianProjection p))).map
        (cocartesianCriticalOver m r).op) := by
    apply (overParameterBoundary_terminal_lifting_iff _ _).mp
    intro n
    exact cocartesianCriticalOver_boundary_lifting m n r p
  exact (modelCategoryQuillen.I.rlp.arrow_iso_iff
    (overMappingRestrictionTargetIso .maximal (cocartesianCriticalOver m r) e)).mpr h

/-- Each actual whole cocartesian critical slice cell is weak for the full intrinsic target testing class. -/
theorem cocartesianCriticalOver_weak {B : SSet.{u}} [Quasicategory B]
    (m : ℕ) (r : cocartesianCriticalTarget.{u} m ⟶ max B) :
    cocartesianWeakEquivalences B (cocartesianCriticalOver m r) := by
  apply (cocartesianWeakEquivalences_iff _).mpr
  intro Y
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _
    (cocartesianCriticalOver_mapping_rlp m r Y)

end SSet.Marked
