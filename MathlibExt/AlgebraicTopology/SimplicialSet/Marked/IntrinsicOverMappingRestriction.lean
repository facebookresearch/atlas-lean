/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntrinsicMappingRestriction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeTargetNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FibrantMappingSpaces

/-!
# Whole original source restrictions in intrinsic marked slices

The original target marking is transported only through the canonical
identity marking isomorphism, retaining its underlying total map and
original base equation. The already proved whole-prism source restriction
therefore applies to every actual intrinsic object of the original slice,
not just the particular canonical marked record.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

/-- Every original marked slice mono restricts mapping spaces into the supplied intrinsic cartesian target
  by a Kan fibration. -/
theorem overMappingFunctor_cartesian_map_fibration {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) [Mono i] (Y : CartesianOver B) :
    Fibration ((overMappingFunctor .maximal (max B) Y.obj).map i.op) := by
  let p : Y.obj.left.toSSet ⟶ B := Y.obj.hom.hom
  let _ : CartesianFibration p := Y.property.1
  let e : Y.obj.left ≅ cartesian p := cartesianMarkingIso p Y.property.2
  let E : Y.obj ≅ Over.mk (cartesianProjection p) := Over.isoMk e (Hom.ext rfl)
  let s := overMappingRestrictionTargetIso .maximal i E
  let _ : Mono i.left := inferInstance
  have h : Fibration ((overMappingFunctor .maximal (max B) (Over.mk (cartesianProjection p))).map i.op) :=
    cartesian_relativeMappingPre_fibration i.left X.hom X'.hom p (Over.w i)
  exact (modelCategoryQuillen.fibration_iff _).mpr
    ((modelCategoryQuillen.J.rlp.arrow_mk_iso_iff s).mpr ((modelCategoryQuillen.fibration_iff _).mp h))

/-- Every original marked slice mono restricts mapping spaces into the supplied intrinsic cocartesian target
  by a Kan fibration. -/
theorem overMappingFunctor_cocartesian_map_fibration {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) [Mono i] (Y : CocartesianOver B) :
    Fibration ((overMappingFunctor .maximal (max B) Y.obj).map i.op) := by
  let p : Y.obj.left.toSSet ⟶ B := Y.obj.hom.hom
  let _ : CocartesianFibration p := Y.property.1
  let e : Y.obj.left ≅ cocartesian p := cocartesianMarkingIso p Y.property.2
  let E : Y.obj ≅ Over.mk (cocartesianProjection p) := Over.isoMk e (Hom.ext rfl)
  let s := overMappingRestrictionTargetIso .maximal i E
  let _ : Mono i.left := inferInstance
  have h : Fibration ((overMappingFunctor .maximal (max B) (Over.mk (cocartesianProjection p))).map i.op) :=
    cocartesian_relativeMappingPre_fibration i.left X.hom X'.hom p (Over.w i)
  exact (modelCategoryQuillen.fibration_iff _).mpr
    ((modelCategoryQuillen.J.rlp.arrow_mk_iso_iff s).mpr ((modelCategoryQuillen.fibration_iff _).mp h))

end SSet.Marked
