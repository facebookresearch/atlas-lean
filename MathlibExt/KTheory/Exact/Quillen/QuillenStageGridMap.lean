/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridLift
public import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShellFunctorMap

/-!
# Exact-functor maps of degreewise Quillen Stage-grid lifts

An additive exact functor acts on retained Quillen simplices and on raw
Stage-grid agreements.  The exact-functor comparison for extracted Quillen
simplices identifies the mapped material Stage with the mapped retained
simplex, so this action restricts to the full subcategory of lift agreements.

The resulting degreewise map commutes strictly with the material-Stage and
retained-Q projections.  This file constructs no outer-reindex coherence,
nerve, diagonal or realization map, weak equivalence, group comparison,
spectrum map, or Q/S equivalence.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v₁ u₁ v₂ u₂

namespace AlgebraicKTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

local instance quillenStageGridMapWaldhausenC : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

local instance quillenStageGridMapWaldhausenD : WaldhausenCategoryWithoutGluing D :=
  ExactCategory.waldhausenCategory D

/-- The exact-functor action on retained Quillen simplices, regarded as a
functor between discrete categories. -/
noncomputable def quillenQSimplexDiscreteMap (a : SimplexCategory) :
    Discrete (QuillenQSimplex C a) ⥤ Discrete (QuillenQSimplex D a) :=
  Discrete.functor (fun q : QuillenQSimplex C a => Discrete.mk
    (((QuillenQ.map F).mapComposableArrows a.len).obj q))

@[simp]
theorem quillenQSimplexDiscreteMap_obj_as
    (a : SimplexCategory) (q : Discrete (QuillenQSimplex C a)) :
    ((quillenQSimplexDiscreteMap F a).obj q).as =
      ((QuillenQ.map F).mapComposableArrows a.len).obj q.as :=
  rfl

/-- The discrete inclusion commutes strictly with the exact-functor action
on retained Quillen simplices. -/
theorem quillenQSimplexDiscreteInclusion_map
    (a : SimplexCategory) :
    quillenQSimplexDiscreteInclusion C a ⋙
        (QuillenQ.map F).mapComposableArrows a.len =
      quillenQSimplexDiscreteMap F a ⋙
        quillenQSimplexDiscreteInclusion D a := by
  apply Discrete.functor_ext
  intro q
  rfl

/-- Exact-functor action on raw Stage-grid agreements. -/
noncomputable def quillenStageGridAgreementMap
    (a : SimplexCategory) :
    QuillenStageGridAgreement C a ⥤ QuillenStageGridAgreement D a :=
  Comma.map
    (F₁ := mapStageWeak C D F (edgewiseQ.obj a).len)
    (F₂ := quillenQSimplexDiscreteMap F a)
    (F := (QuillenQ.map F).mapComposableArrows a.len)
    (edgewiseStageQuillenSimplexFunctor_mapIso F a).hom
    (eqToIso (quillenQSimplexDiscreteInclusion_map F a)).hom

@[simp]
theorem quillenStageGridAgreementMap_obj_left
    (a : SimplexCategory) (X : QuillenStageGridAgreement C a) :
    ((quillenStageGridAgreementMap F a).obj X).left =
      (mapStageWeak C D F (edgewiseQ.obj a).len).obj X.left :=
  rfl

@[simp]
theorem quillenStageGridAgreementMap_obj_right_as
    (a : SimplexCategory) (X : QuillenStageGridAgreement C a) :
    ((quillenStageGridAgreementMap F a).obj X).right.as =
      ((QuillenQ.map F).mapComposableArrows a.len).obj X.right.as :=
  rfl

@[simp]
theorem quillenStageGridAgreementMap_obj_hom
    (a : SimplexCategory) (X : QuillenStageGridAgreement C a) :
    ((quillenStageGridAgreementMap F a).obj X).hom =
      (edgewiseStageQuillenSimplexFunctor_mapIso F a).hom.app X.left ≫
        ((QuillenQ.map F).mapComposableArrows a.len).map X.hom ≫
        (eqToIso (quillenQSimplexDiscreteInclusion_map F a)).hom.app
          X.right :=
  rfl

set_option linter.style.haveILetI false in
/-- The exact-functor action carries an isomorphism agreement to an
isomorphism agreement. -/
theorem quillenStageGridAgreementMap_isLift
    {a : SimplexCategory} (X : QuillenStageGridLift C a) :
    IsIso ((quillenStageGridAgreementMap F a).obj X.obj).hom := by
  have hX := X.property
  change IsIso X.obj.hom at hX
  letI : IsIso X.obj.hom := hX
  change IsIso
    ((edgewiseStageQuillenSimplexFunctor_mapIso F a).hom.app X.obj.left ≫
      ((QuillenQ.map F).mapComposableArrows a.len).map X.obj.hom ≫
      (eqToIso (quillenQSimplexDiscreteInclusion_map F a)).hom.app
        X.obj.right)
  infer_instance

/-- Degreewise exact-functor action on Quillen Stage-grid lifts. -/
noncomputable def quillenStageGridLiftMap
    (a : SimplexCategory) :
    QuillenStageGridLift C a ⥤ QuillenStageGridLift D a where
  obj X := ⟨(quillenStageGridAgreementMap F a).obj X.obj,
    quillenStageGridAgreementMap_isLift F X⟩
  map f := ObjectProperty.homMk
    ((quillenStageGridAgreementMap F a).map f.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · simp
    · exact Subsingleton.elim _ _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · simp
    · exact Subsingleton.elim _ _

@[simp]
theorem quillenStageGridLiftMap_obj_grid
    (a : SimplexCategory) (X : QuillenStageGridLift C a) :
    ((quillenStageGridLiftMap F a).obj X).grid =
      (mapStageWeak C D F (edgewiseQ.obj a).len).obj X.grid :=
  rfl

@[simp]
theorem quillenStageGridLiftMap_obj_q
    (a : SimplexCategory) (X : QuillenStageGridLift C a) :
    ((quillenStageGridLiftMap F a).obj X).q =
      ((QuillenQ.map F).mapComposableArrows a.len).obj X.q :=
  rfl

@[simp]
theorem quillenStageGridLiftMap_map_hom_left
    (a : SimplexCategory) {X Y : QuillenStageGridLift C a} (f : X ⟶ Y) :
    ((quillenStageGridLiftMap F a).map f).hom.left =
      (mapStageWeak C D F (edgewiseQ.obj a).len).map f.hom.left :=
  rfl

@[simp]
theorem quillenStageGridLiftMap_map_hom_right
    (a : SimplexCategory) {X Y : QuillenStageGridLift C a} (f : X ⟶ Y) :
    ((quillenStageGridLiftMap F a).map f).hom.right =
      (quillenQSimplexDiscreteMap F a).map f.hom.right :=
  rfl

/-- The degreewise lift map commutes strictly with the material-Stage
projection. -/
theorem quillenStageGridLiftMap_gridProjection
    (a : SimplexCategory) :
    quillenStageGridLiftMap F a ⋙ quillenStageGridProjection D a =
      quillenStageGridProjection C a ⋙
        mapStageWeak C D F (edgewiseQ.obj a).len := by
  rfl

/-- The degreewise lift map commutes strictly with the retained discrete
Quillen-simplex projection. -/
theorem quillenStageGridLiftMap_qProjection
    (a : SimplexCategory) :
    quillenStageGridLiftMap F a ⋙ quillenStageGridQProjection D a =
      quillenStageGridQProjection C a ⋙
        quillenQSimplexDiscreteMap F a := by
  rfl

end AlgebraicKTheory

end
