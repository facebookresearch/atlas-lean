/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeMappingCoreIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeTargetIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeMappingZero
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso

/-!
# Native Kan mapping spaces of the original marked fibration carriers

The actual Cartesian and cocartesian fibration objects retain their supplied
marked total spaces. Their intrinsic edge-class equation gives the identity
marked isomorphism to the canonical marking, so the native fixed-base core
comparison proves Kan mapping spaces for these original objects. Vertices
are exactly their original marked maps over the base.

These are the existing fibration-carrier categories. No marked model
structure or straightening equivalence is asserted.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

/-- The intrinsic Cartesian edge equation gives the marked identity isomorphism on the original carrier. -/
def cartesianMarkingIso {Y : Marked.{u}} {B : SSet.{u}} (p : Y.toSSet ⟶ B)
    [InnerFibration p] [Quasicategory B]
    (h : ∀ e : Y.toSSet _⦋1⦌, e ∈ Y.marking ↔ CartesianEdge.IsPCartesian p (SSet.yonedaEquiv.symm e)) :
    Y ≅ cartesian p := isoMk (Iso.refl Y.toSSet) h

/-- The cocartesian edge equation gives the same underlying identity isomorphism. -/
def cocartesianMarkingIso {Y : Marked.{u}} {B : SSet.{u}} (p : Y.toSSet ⟶ B)
    [InnerFibration p] [Quasicategory B]
    (h : ∀ e : Y.toSSet _⦋1⦌, e ∈ Y.marking ↔ CocartesianEdge.IsPCocartesian p (SSet.yonedaEquiv.symm e)) :
    Y ≅ cocartesian p := isoMk (Iso.refl Y.toSSet) h

/-- The original Cartesian-fibration mapping complex retains the supplied total objects and projections. -/
def CartesianOver.mappingComplex {B : SSet.{u}} (X Y : CartesianOver B) : SSet.{u} :=
  relativeMappingComplex .maximal X.obj.hom Y.obj.hom

/-- The original cocartesian-fibration mapping complex uses those same marked fixed-base maps. -/
def CocartesianOver.mappingComplex {B : SSet.{u}} (X Y : CocartesianOver B) : SSet.{u} :=
  relativeMappingComplex .maximal X.obj.hom Y.obj.hom

/-- Actual Cartesian-fibration carriers have native Kan mapping spaces over every quasicategory base. -/
theorem CartesianOver.mappingComplex_kanComplex {B : SSet.{u}} [Quasicategory B]
    (X Y : CartesianOver B) : KanComplex (CartesianOver.mappingComplex X Y) := by
  let p : Y.obj.left.toSSet ⟶ B := Y.obj.hom.hom
  let _ : CartesianFibration p := Y.property.1
  let _ : InnerFibration p := inferInstance
  let e := cartesianMarkingIso p Y.property.2
  have he : e.hom ≫ cartesianProjection p = Y.obj.hom := Hom.ext rfl
  let j := relativeMappingTargetIso .maximal X.obj.hom e Y.obj.hom
    (cartesianProjection p) he
  let _ : KanComplex (relativeMappingComplex .maximal X.obj.hom (cartesianProjection p)) :=
    cartesian_relativeMapping_kanComplex X.obj.hom p
  let _ : IsIso j.hom := inferInstance
  let _ : Fibration j.hom := by
    rw [fibration_iff, modelCategoryQuillen.fibrations_eq]
    exact modelCategoryQuillen.J.rlp_of_isIso j.hom
  change KanComplex (relativeMappingComplex .maximal X.obj.hom Y.obj.hom)
  exact isFibrant_of_fibration j.hom

/-- The same native fibrancy statement holds for the supplied cocartesian-fibration objects. -/
theorem CocartesianOver.mappingComplex_kanComplex {B : SSet.{u}} [Quasicategory B]
    (X Y : CocartesianOver B) : KanComplex (CocartesianOver.mappingComplex X Y) := by
  let p : Y.obj.left.toSSet ⟶ B := Y.obj.hom.hom
  let _ : CocartesianFibration p := Y.property.1
  let _ : InnerFibration p := inferInstance
  let e := cocartesianMarkingIso p Y.property.2
  have he : e.hom ≫ cocartesianProjection p = Y.obj.hom := Hom.ext rfl
  let j := relativeMappingTargetIso .maximal X.obj.hom e Y.obj.hom
    (cocartesianProjection p) he
  let _ : KanComplex (relativeMappingComplex .maximal X.obj.hom (cocartesianProjection p)) :=
    cocartesian_relativeMapping_kanComplex X.obj.hom p
  let _ : IsIso j.hom := inferInstance
  let _ : Fibration j.hom := by
    rw [fibration_iff, modelCategoryQuillen.fibrations_eq]
    exact modelCategoryQuillen.J.rlp_of_isIso j.hom
  change KanComplex (relativeMappingComplex .maximal X.obj.hom Y.obj.hom)
  exact isFibrant_of_fibration j.hom

/-- The actual Cartesian mapping vertices are exactly the original Cartesian-edge preserving base maps. -/
def CartesianOver.mappingZeroEquiv {B : SSet.{u}} (X Y : CartesianOver B) :
    (CartesianOver.mappingComplex X Y) _⦋0⦌ ≃ (X ⟶ Y) :=
  (relativeMappingZeroEquiv .maximal X.obj.hom Y.obj.hom).trans
    { toFun := fun f => ObjectProperty.homMk (Over.homMk f.val f.property)
      invFun := fun f => ⟨f.hom.left, Over.w f.hom⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => by
        apply ObjectProperty.hom_ext
        apply CostructuredArrow.hom_ext
        rfl }

/-- The cocartesian mapping vertices likewise retain precisely the original ordinary morphisms. -/
def CocartesianOver.mappingZeroEquiv {B : SSet.{u}} (X Y : CocartesianOver B) :
    (CocartesianOver.mappingComplex X Y) _⦋0⦌ ≃ (X ⟶ Y) :=
  (relativeMappingZeroEquiv .maximal X.obj.hom Y.obj.hom).trans
    { toFun := fun f => ObjectProperty.homMk (Over.homMk f.val f.property)
      invFun := fun f => ⟨f.hom.left, Over.w f.hom⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => by
        apply ObjectProperty.hom_ext
        apply CostructuredArrow.hom_ext
        rfl }

end SSet.Marked
