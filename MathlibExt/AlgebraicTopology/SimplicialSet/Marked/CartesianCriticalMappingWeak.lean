/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalParameterCorner
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterArrowComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterTerminalComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeTargetNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianWeakEquivalences
import Mathlib.CategoryTheory.LiftingProperties.Over

/-!
# Actual mapping weakness of the original cartesian critical cells

Each original whole critical simplex may have any supplied marked map
to the maximally marked base. Its full scalar boundary corner retains
that base map and lifts against the intrinsic cartesian projection.
The original mapping restrictions therefore have all boundary lifts and
are weak. The selected critical last edge, all marks and the original
non-Kan quasicategory base are retained.
-/

noncomputable section
universe u
open CategoryTheory Limits
open scoped Simplicial

namespace SSet.Marked

/-- The original marked critical cell lies over its supplied whole original target-to-base map. -/
def cartesianCriticalOver {B : SSet.{u}} (m : ℕ) (r : cartesianCriticalTarget.{u} m ⟶ max B) :
    Over.mk (cartesianCriticalCell.{u} m ≫ r) ⟶ Over.mk r :=
  Over.homMk (cartesianCriticalCell.{u} m) rfl

/-- Every full boundary-parameter square of the original critical slice cell lifts against the actual
  canonical cartesian projection. -/
theorem cartesianCriticalOver_boundary_lifting {B E : SSet.{u}} [Quasicategory B]
    (m n : ℕ) (r : cartesianCriticalTarget.{u} m ⟶ max B)
    (p : E ⟶ B) [InnerFibration p] :
    HasLiftingProperty (overParameterPushoutProduct (boundary.{u} n).ι (cartesianCriticalOver m r))
      (Over.mkIdTerminal.from (Over.mk (cartesianProjection p))) := by
  let f := cartesianCriticalOver m r
  let t := Over.mkIdTerminal.from (Over.mk (cartesianProjection p))
  have ht : t.left = cartesianProjection p := Over.mkIdTerminal_from_left _
  let _ : HasLiftingProperty
      (parameterPushoutProduct (boundary.{u} n).ι f.left) t.left :=
    ht.symm ▸ cartesianCriticalParameter_boundary_lifting m n p
  let _ : HasLiftingProperty (overParameterPushoutProduct (boundary.{u} n).ι f).left t.left :=
    (HasLiftingProperty.iff_of_arrow_iso_left (overParameterMarkedArrowIso _ f) t.left).mpr inferInstance
  exact HasLiftingProperty.over _ t

/-- The original critical cell restriction has the full native mapping boundary-right property into every
  intrinsic cartesian target. -/
theorem cartesianCriticalOver_mapping_rlp {B : SSet.{u}} [Quasicategory B]
    (m : ℕ) (r : cartesianCriticalTarget.{u} m ⟶ max B) (Y : CartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp
      ((overMappingFunctor .maximal (max B) Y.obj).map (cartesianCriticalOver m r).op) := by
  let p : Y.obj.left.toSSet ⟶ B := Y.obj.hom.hom
  let _ : CartesianFibration p := Y.property.1
  let e : Y.obj ≅ Over.mk (cartesianProjection p) :=
    Over.isoMk (cartesianMarkingIso p Y.property.2) (Hom.ext rfl)
  have h : modelCategoryQuillen.I.{u}.rlp
      ((overMappingFunctor .maximal (max B) (Over.mk (cartesianProjection p))).map
        (cartesianCriticalOver m r).op) := by
    apply (overParameterBoundary_terminal_lifting_iff _ _).mp
    intro n
    exact cartesianCriticalOver_boundary_lifting m n r p
  exact (modelCategoryQuillen.I.rlp.arrow_iso_iff
    (overMappingRestrictionTargetIso .maximal (cartesianCriticalOver m r) e)).mpr h

/-- Each actual whole cartesian critical slice cell is weak for the full intrinsic target testing class. -/
theorem cartesianCriticalOver_weak {B : SSet.{u}} [Quasicategory B]
    (m : ℕ) (r : cartesianCriticalTarget.{u} m ⟶ max B) :
    cartesianWeakEquivalences B (cartesianCriticalOver m r) := by
  apply (cartesianWeakEquivalences_iff _).mpr
  intro Y
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _
    (cartesianCriticalOver_mapping_rlp m r Y)

end SSet.Marked
