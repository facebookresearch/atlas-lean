/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverMappingFunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FibrantMappingSpaces

/-!
# Original fixed-base mapping spaces into intrinsic fibrant targets

An arbitrary marked source over the original quasicategory base has a
native Kan relative mapping space into an intrinsically marked Cartesian
or cocartesian fibration. The identity marked comparison transports the
proved original relative core/prism theorem, retaining the same supplied
source, marks and whole base maps. The source need not itself be fibrant.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

/-- Every original marked source has a genuine Kan mapping space into the supplied intrinsic Cartesian target. -/
theorem overMappingFunctor_cartesian_kan {B : SSet.{u}} [Quasicategory B]
    (X : Over (max B)) (Y : CartesianOver B) :
    KanComplex ((overMappingFunctor .maximal (max B) Y.obj).obj (Opposite.op X)) := by
  let p : Y.obj.left.toSSet ⟶ B := Y.obj.hom.hom
  let _ : CartesianFibration p := Y.property.1
  let _ : InnerFibration p := inferInstance
  let e := cartesianMarkingIso p Y.property.2
  have he : e.hom ≫ cartesianProjection p = Y.obj.hom := Hom.ext rfl
  let j := relativeMappingTargetIso .maximal X.hom e Y.obj.hom (cartesianProjection p) he
  let _ : KanComplex (relativeMappingComplex .maximal X.hom (cartesianProjection p)) :=
    cartesian_relativeMapping_kanComplex X.hom p
  let _ : IsIso j.hom := inferInstance
  let _ : Fibration j.hom := by
    rw [fibration_iff, modelCategoryQuillen.fibrations_eq]
    exact modelCategoryQuillen.J.rlp_of_isIso j.hom
  change KanComplex (relativeMappingComplex .maximal X.hom Y.obj.hom)
  exact isFibrant_of_fibration j.hom

/-- The original arbitrary-source result also holds for the supplied intrinsic cocartesian target. -/
theorem overMappingFunctor_cocartesian_kan {B : SSet.{u}} [Quasicategory B]
    (X : Over (max B)) (Y : CocartesianOver B) :
    KanComplex ((overMappingFunctor .maximal (max B) Y.obj).obj (Opposite.op X)) := by
  let p : Y.obj.left.toSSet ⟶ B := Y.obj.hom.hom
  let _ : CocartesianFibration p := Y.property.1
  let _ : InnerFibration p := inferInstance
  let e := cocartesianMarkingIso p Y.property.2
  have he : e.hom ≫ cocartesianProjection p = Y.obj.hom := Hom.ext rfl
  let j := relativeMappingTargetIso .maximal X.hom e Y.obj.hom (cocartesianProjection p) he
  let _ : KanComplex (relativeMappingComplex .maximal X.hom (cocartesianProjection p)) :=
    cocartesian_relativeMapping_kanComplex X.hom p
  let _ : IsIso j.hom := inferInstance
  let _ : Fibration j.hom := by
    rw [fibration_iff, modelCategoryQuillen.fibrations_eq]
    exact modelCategoryQuillen.J.rlp_of_isIso j.hom
  change KanComplex (relativeMappingComplex .maximal X.hom Y.obj.hom)
  exact isFibrant_of_fibration j.hom

end SSet.Marked
