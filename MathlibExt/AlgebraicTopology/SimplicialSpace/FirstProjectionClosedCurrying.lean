/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.FirstProjectionClosedCoherence

/-!
# Literal currying under the first-JT closed comparison

The actual comparison commutes with scalar transposes and with the entire
internal currying Iso. The product identification is the canonical right
product Iso, including the order of both source coordinates.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped MonoidalCategory SimplicialSpace.Cartesian

namespace SimplicialSpace.FirstProjection

private local instance rightLimits : PreservesLimitsOfSize.{0, 0} right.{u} :=
  adjunction.rightAdjoint_preservesLimits

private local instance rightFiniteProducts : PreservesFiniteProducts right.{u} where
  preserves _ := rightLimits.preservesLimitsOfShape

private local instance rightMonoidal : right.{u}.Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts right

private theorem rightMu (W V : SimplicialSpace.{u}) :
    Functor.LaxMonoidal.μ right W V = (rightProductIso W V).inv :=
  Functor.Monoidal.μ_of_cartesianMonoidalCategory right W V

/-- Every original transpose becomes the native scalar transpose of its literal evaluation mate. -/
theorem comparison_curry (W P V : SimplicialSpace.{u}) (f : W ⊗ P ⟶ V) :
    right.map (MonoidalClosed.curry f) ≫ comparison W V =
      MonoidalClosed.curry ((rightProductIso W P).inv ≫ right.map f) := by
  apply uncurry_injective
  rw [uncurry_natural_left, comparison_evaluation, uncurry_curry, ← rightMu, ← rightMu,
    Functor.LaxMonoidal.μ_natural_right_assoc, ← Functor.map_comp,
    ← uncurry_eq, uncurry_curry]

/-- The actual curve of constant CSS functors becomes the curve of native constant functors. -/
theorem comparison_constants (W V : SimplicialSpace.{u}) :
    right.map (MonoidalClosed.curry (CartesianMonoidalCategory.snd W V)) ≫ comparison W V =
      MonoidalClosed.curry (CartesianMonoidalCategory.snd (right.obj W) (right.obj V)) := by
  rw [comparison_curry, ← CartesianMonoidalCategory.prodComparison_snd,
    ← rightProductIso_hom, Iso.inv_hom_id_assoc]

private theorem uncurryCurryMap {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]
    (A B D P : C) (f : P ⟶ (ihom (A ⊗ B)).obj D) :
    uncurry (uncurry (f ≫ (ihomCurryIso A B D).hom)) =
      (α_ A B P).inv ≫ uncurry f := by
  change uncurry (uncurry (f ≫ ihomCurry A B D)) = _
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_uncurry_ihomCurry,
    associator_inv_naturality_right_assoc, ← uncurry_eq]

/-- The full internal currying Iso commutes with the same actual closed comparison. -/
theorem comparison_currying (W V U : SimplicialSpace.{u}) :
    comparison (W ⊗ V) U ≫ (pre (rightProductIso W V).inv).app (right.obj U) ≫
        (ihomCurryIso (right.obj W) (right.obj V) (right.obj U)).hom =
      right.map ((ihomCurryIso W V U).hom) ≫ comparison V ((ihom W).obj U) ≫
        (ihom (right.obj V)).map (comparison W U) := by
  apply uncurry_injective
  apply uncurry_injective
  rw [← Category.assoc, uncurryCurryMap, uncurry_pre_app, comparison_evaluation]
  change (α_ (right.obj W) (right.obj V) (right.obj ((ihom (W ⊗ V)).obj U))).inv ≫
      (rightProductIso W V).inv ▷ right.obj ((ihom (W ⊗ V)).obj U) ≫
        (rightProductIso (W ⊗ V) ((ihom (W ⊗ V)).obj U)).inv ≫
          right.map ((ihom.ev (W ⊗ V)).app U) =
    uncurry (uncurry (right.map (curry (curry
      ((α_ W V ((ihom (W ⊗ V)).obj U)).inv ≫ (ihom.ev (W ⊗ V)).app U))) ≫
        comparison V ((ihom W).obj U) ≫ (ihom (right.obj V)).map (comparison W U)))
  have hV := comparison_curry V ((ihom (W ⊗ V)).obj U) ((ihom W).obj U)
    (MonoidalClosed.curry ((α_ W V ((ihom (W ⊗ V)).obj U)).inv ≫ (ihom.ev (W ⊗ V)).app U))
  have hW := comparison_curry W (V ⊗ (ihom (W ⊗ V)).obj U) U
    ((α_ W V ((ihom (W ⊗ V)).obj U)).inv ≫ (ihom.ev (W ⊗ V)).app U)
  conv_rhs =>
    rw [← Category.assoc]
    erw [hV]
    rw [← curry_natural_right, uncurry_curry, Category.assoc, uncurry_natural_left]
    erw [hW]
    rw [uncurry_curry]
  simp only [← rightMu, Functor.map_comp]
  rw [Functor.LaxMonoidal.associativity_inv_assoc]

end SimplicialSpace.FirstProjection
