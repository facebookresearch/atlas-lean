/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Enriched.MappingParametrized
public import MathlibExt.CategoryTheory.Enriched.GradedTensor
public import MathlibExt.CategoryTheory.Enriched.GradingConvention
public import MathlibExt.CategoryTheory.Enriched.ScalarCotensor
public import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# The two actual parametrized adjunctions for enriched diagram scalars

The complete existing graded tensor, cotensor and weighted-end bijections
are reused. Their projection formulas construct the two parametrized
adjunctions needed by mixed pushout-product lifting. Every scalar, diagram
and target arrow remains the original one.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section

universe uA uV vV

open CategoryTheory Limits MonoidalCategory BraidedCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.ScalarParametrizedAdjunctions

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- The original scalar tensor and cotensor correspondence, with the actual central grade. -/
private def tensorCotensorHomEquiv (M : V) (F G : EnrichedFunctorCat V A) :
    (tensorLeftObject M F ⟶ G) ≃ (F ⟶ cotensorObject M G) :=
  (gradedTensorHomEquiv ((Center.ofBraided V).obj M) F G).symm.trans
    (gradedCotensorEquiv ((Center.ofBraided V).obj M) F G)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar/cotensor transposition is the original coefficient curry at each object. -/
private theorem tensorCotensorHomEquiv_component (M : V) (F G : EnrichedFunctorCat V A)
    (f : tensorLeftObject M F ⟶ G) (a : A) :
    component (tensorCotensorHomEquiv M F G f) a = MonoidalClosed.curry (component f a) := by
  unfold tensorCotensorHomEquiv
  rw [Equiv.trans_apply]
  erw [gradedCotensorEquiv_apply, gradedToCotensor_component]
  exact congrArg MonoidalClosed.curry
    (gradedTensorOfUnit_gradeFirstComponent ((Center.ofBraided V).obj M) f a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse transpose uses the same original coefficient uncurry. -/
private theorem tensorCotensorHomEquiv_symm_component (M : V) (F G : EnrichedFunctorCat V A)
    (f : F ⟶ cotensorObject M G) (a : A) :
    component ((tensorCotensorHomEquiv M F G).symm f) a =
      MonoidalClosed.uncurry (component f a) := by
  unfold tensorCotensorHomEquiv
  change component (gradedTensorToUnit ((Center.ofBraided V).obj M)
    ((gradedCotensorEquiv ((Center.ofBraided V).obj M) F G).symm f)) a = _
  rw [gradedCotensorEquiv_symm_apply]
  rw [gradedTensorToUnit_component, cotensorToGraded_gradeFirst]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Coefficient cotensoring retains all original contravariant scalar maps. -/
def cotensorBifunctor : Vᵒᵖ ⥤ EnrichedFunctorCat V A ⥤ EnrichedFunctorCat V A where
  obj M := EnrichedFunctorCat.cotensor M.unop
  map u :=
    { app F := cotensorScalarMap u.unop F
      naturality F G f := cotensorScalarMap_naturality u.unop f }
  map_id M := by
    apply NatTrans.ext
    funext F
    exact cotensorScalarMap_id M.unop F
  map_comp u v := by
    apply NatTrans.ext
    funext F
    exact cotensorScalarMap_comp v.unop u.unop F

set_option backward.isDefEq.respectTransparency false in
/-- The entire source transpose is natural in the original diagram arrow. -/
private theorem cotensor_inverse_source (M : V) {F F' G : EnrichedFunctorCat V A}
    (u : F' ⟶ F) (f : F ⟶ cotensorObject M G) :
    (tensorCotensorHomEquiv M F' G).symm (u ≫ f) =
      tensorLeftMap M u ≫ (tensorCotensorHomEquiv M F G).symm f := by
  apply hom_ext
  intro a
  rw [tensorCotensorHomEquiv_symm_component, component_comp, component_comp,
    tensorLeftMap_component, tensorCotensorHomEquiv_symm_component,
    MonoidalClosed.uncurry_natural_left]

set_option backward.isDefEq.respectTransparency false in
/-- The target transpose retains the original pointwise cotensor map. -/
private theorem cotensor_forward_target (M : V) {F G G' : EnrichedFunctorCat V A}
    (f : tensorLeftObject M F ⟶ G) (u : G ⟶ G') :
    tensorCotensorHomEquiv M F G' (f ≫ u) =
      tensorCotensorHomEquiv M F G f ≫ cotensorMap M u := by
  apply hom_ext
  intro a
  rw [tensorCotensorHomEquiv_component, component_comp, component_comp,
    tensorCotensorHomEquiv_component, cotensorMap_component,
    MonoidalClosed.curry_natural_right]

set_option backward.isDefEq.respectTransparency false in
/-- The scalar tensor/cotensor adjunctions have their complete original parameter naturality. -/
@[no_expose]
def tensorCotensorParametrized :
    EnrichedFunctorCat.tensorBifunctor (V := V) (A := A) ⊣₂ cotensorBifunctor :=
  ParametrizedAdjunction.mk'
    (fun M => Adjunction.mkOfHomEquiv
      { homEquiv := fun F G => tensorCotensorHomEquiv M F G
        homEquiv_naturality_left_symm := cotensor_inverse_source M
        homEquiv_naturality_right := cotensor_forward_target M })
    (by
      intro M N u F G f
      rw [Adjunction.mkOfHomEquiv_homEquiv, Adjunction.mkOfHomEquiv_homEquiv]
      change tensorCotensorHomEquiv M F G (scalarTensorMap u F ≫ f) =
        tensorCotensorHomEquiv N F G f ≫ cotensorScalarMap u G
      apply hom_ext
      intro a
      rw [tensorCotensorHomEquiv_component, component_comp, scalarTensorMap_component,
        component_comp, tensorCotensorHomEquiv_component, cotensorScalarMap_component,
        MonoidalClosed.curry_pre_app])

variable [HasProducts.{uA} V] [HasEqualizers V]

/-- The original graded/end and graded/scalar bijections, including every scalar coefficient. -/
private def endTensorHomEquiv (F G : EnrichedFunctorCat V A) (M : V) :
    (M ⟶ WeightedEndVariance.object F G) ≃ (tensorLeftObject M F ⟶ G) :=
  (GradingConvention.endHomEquiv F.toEnrichedFunctor G.toEnrichedFunctor M).trans
    (gradedTensorHomEquiv ((Center.ofBraided V).obj M) F G)

set_option backward.isDefEq.respectTransparency false in
/-- The actual full end transpose has the canonical grade-first coefficient formula. -/
private theorem endTensorHomEquiv_component (F G : EnrichedFunctorCat V A) (M : V)
    (h : M ⟶ WeightedEndVariance.object F G) (a : A) :
    component (endTensorHomEquiv F G M h) a =
      (β_ M (F.toEnrichedFunctor.obj a)).hom ≫
        MonoidalClosed.uncurry (h ≫ WeightedEndVariance.projection F G a) := by
  unfold endTensorHomEquiv
  rw [Equiv.trans_apply, GradingConvention.endHomEquiv_apply]
  change component (gradedTensorToUnit ((Center.ofBraided V).obj M)
    (GradingConvention.endToPositive F.toEnrichedFunctor G.toEnrichedFunctor h)) a = _
  rw [gradedTensorToUnit_component]
  change (β_ M (F.toEnrichedFunctor.obj a)).hom ≫
    MonoidalClosed.uncurry
      ((GradingConvention.endToPositive F.toEnrichedFunctor G.toEnrichedFunctor h).app a) = _
  rw [GradingConvention.endToPositive_app_symmetric]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse retains the entire original half-braiding before coefficient currying. -/
private theorem endTensorHomEquiv_symm_projection (F G : EnrichedFunctorCat V A) (M : V)
    (f : tensorLeftObject M F ⟶ G) (a : A) :
    (endTensorHomEquiv F G M).symm f ≫ WeightedEndVariance.projection F G a =
      MonoidalClosed.curry ((β_ M (F.toEnrichedFunctor.obj a)).inv ≫ component f a) := by
  unfold endTensorHomEquiv
  change (GradingConvention.endHomEquiv F.toEnrichedFunctor G.toEnrichedFunctor M).symm
    ((gradedTensorHomEquiv ((Center.ofBraided V).obj M) F G).symm f) ≫
      WeightedEndVariance.projection F G a = _
  rw [GradingConvention.endHomEquiv_symm_apply]
  rw [GradingConvention.endFromPositive_symmetric_π]
  change (gradedTensorOfUnit ((Center.ofBraided V).obj M) f).app a = _
  rw [gradedTensorOfUnit_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The forward transpose is natural in every original coefficient map. -/
private theorem end_forward_scalar (F G : EnrichedFunctorCat V A) {M N : V}
    (u : M ⟶ N) (h : N ⟶ WeightedEndVariance.object F G) :
    endTensorHomEquiv F G M (u ≫ h) = scalarTensorMap u F ≫ endTensorHomEquiv F G N h := by
  apply hom_ext
  intro a
  rw [endTensorHomEquiv_component, component_comp, scalarTensorMap_component,
    endTensorHomEquiv_component, Category.assoc, MonoidalClosed.uncurry_natural_left,
    ← braiding_naturality_left_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse transpose is natural in every complete original target transformation. -/
private theorem end_inverse_target (F : EnrichedFunctorCat V A)
    {G G' : EnrichedFunctorCat V A} (M : V) (f : tensorLeftObject M F ⟶ G) (u : G ⟶ G') :
    (endTensorHomEquiv F G' M).symm (f ≫ u) =
      (endTensorHomEquiv F G M).symm f ≫ WeightedEndVariance.post F u := by
  apply Enriched.weightedEnd.hom_ext F.toEnrichedFunctor G'.toEnrichedFunctor
  intro a
  simp only [Category.assoc]
  rw [endTensorHomEquiv_symm_projection, component_comp, WeightedEndVariance.post_projection]
  rw [← Category.assoc _ _ ((ihom (F.toEnrichedFunctor.obj a)).map (component u a))]
  erw [endTensorHomEquiv_symm_projection]
  rw [← MonoidalClosed.curry_natural_right]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Construct the complete original tensor/end parametrized adjunction with the checked factory. -/
@[no_expose]
def tensorEndParametrized :
    (WeightedEndVariance.tensorBifunctor (V := V) (I := A)).flip ⊣₂
      WeightedEndVariance.bifunctor :=
  WeightedEndVariance.parametrizedOfProjection
    (fun F => Adjunction.mkOfHomEquiv
      { homEquiv := fun M G => (endTensorHomEquiv F G M).symm
        homEquiv_naturality_left_symm := end_forward_scalar F _
        homEquiv_naturality_right := fun {M G G'} f u => end_inverse_target F M f u })
    endTensorHomEquiv
    (by intro F G M; rw [Adjunction.mkOfHomEquiv_homEquiv])
    endTensorHomEquiv_symm_projection

end CategoryTheory.EnrichedFunctorCat.ScalarParametrizedAdjunctions
