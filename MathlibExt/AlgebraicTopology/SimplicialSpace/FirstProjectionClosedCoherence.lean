/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.FirstProjectionClosedComparison
import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
# Coherence of the actual first-JT closed comparison

The right functor's canonical finite-product structure and its literal
evaluation mate preserve the original identities, composition and currying.
All formulas hold before localization and use the chosen product maps.
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

private local instance rightBraided : right.{u}.Braided :=
  Functor.Braided.ofChosenFiniteProducts right

private theorem rightMu (W V : SimplicialSpace.{u}) :
    Functor.LaxMonoidal.μ right W V = (rightProductIso W V).inv :=
  Functor.Monoidal.μ_of_cartesianMonoidalCategory right W V

/-- The original terminal comparison, needed to retain identity functors. -/
def rightUnitIso : right.obj (𝟙_ SimplicialSpace.{u}) ≅ 𝟙_ SSet.{u} :=
  CartesianMonoidalCategory.preservesTerminalIso right.{u}

private theorem rightEpsilon :
    Functor.LaxMonoidal.ε right.{u} = rightUnitIso.{u}.inv :=
  Functor.Monoidal.ε_of_cartesianMonoidalCategory right.{u}

/-- The comparison is natural in every actual target map. -/
theorem comparison_target (W : SimplicialSpace.{u}) {V U : SimplicialSpace.{u}} (g : V ⟶ U) :
    right.map ((ihom W).map g) ≫ comparison W U =
      comparison W V ≫ (ihom (right.obj W)).map (right.map g) := by
  simp only [comparison_eq_expComparison]
  exact (CategoryTheory.expComparison right W).naturality g

/-- Source restriction retains the original contravariant functor map. -/
theorem comparison_source {W V : SimplicialSpace.{u}} (f : W ⟶ V) (U : SimplicialSpace.{u}) :
    right.map ((pre f).app U) ≫ comparison W U =
      comparison V U ≫ (pre (right.map f)).app (right.obj U) := by
  simp only [comparison_eq_expComparison]
  exact (congrArg (fun t => t.app U)
    (CategoryTheory.expComparison_whiskerLeft right f)).symm

/-- Identity functors are the literal right image of the CSS identities. -/
theorem comparison_identity (W : SimplicialSpace.{u}) :
    rightUnitIso.{u}.inv ≫ right.map (MonoidalClosed.id W) ≫ comparison W W =
      MonoidalClosed.id (right.obj W) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, comparison_evaluation,
    MonoidalClosed.id_eq (right.obj W), uncurry_curry, ← rightMu,
    Functor.LaxMonoidal.μ_natural_right_assoc,
    ← Functor.map_comp, ← uncurry_eq, MonoidalClosed.id_eq W, uncurry_curry, ← rightEpsilon]
  exact (Functor.LaxMonoidal.right_unitality right W).symm

private theorem uncurryComp {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]
    (A B D P Q : C) (f : P ⟶ (ihom A).obj B) (g : Q ⟶ (ihom B).obj D) :
    uncurry ((f ⊗ₘ g) ≫ MonoidalClosed.comp A B D) =
      (α_ A P Q).inv ≫ uncurry f ▷ Q ≫ B ◁ g ≫ (ihom.ev B).app D := by
  rw [uncurry_natural_left, comp_eq, uncurry_curry, compTranspose_eq,
    tensorHom_def, whiskerLeft_comp]
  simp only [Category.assoc]
  rw [associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc,
    whisker_exchange_assoc, ← comp_whiskerRight_assoc, uncurry_eq]
  rfl

/-- Composition is preserved with the actual right product identification. -/
theorem comparison_composition (W V U : SimplicialSpace.{u}) :
    (rightProductIso ((ihom W).obj V) ((ihom V).obj U)).inv ≫
        right.map (MonoidalClosed.comp W V U) ≫ comparison W U =
      (comparison W V ⊗ₘ comparison V U) ≫
        MonoidalClosed.comp (right.obj W) (right.obj V) (right.obj U) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, comparison_evaluation,
    ← rightMu, ← rightMu, Functor.LaxMonoidal.μ_natural_right_assoc,
    ← Functor.map_comp, ← uncurry_eq, comp_eq, uncurry_curry,
    compTranspose_eq, Functor.map_comp, Functor.map_comp,
    Functor.LaxMonoidal.associativity_inv_assoc, ← Functor.LaxMonoidal.μ_natural_left_assoc,
    ← comp_whiskerRight_assoc, rightMu, rightMu,
    uncurryComp, comparison_evaluation, ← uncurry_eq, comparison_evaluation]
  rfl

/-- The original later-then-earlier composition convention retains the same native braiding and maps. -/
theorem comparison_composition_laterFirst (W V U : SimplicialSpace.{u}) :
    (rightProductIso ((ihom V).obj U) ((ihom W).obj V)).inv ≫
        right.map ((β_ ((ihom V).obj U) ((ihom W).obj V)).hom ≫ MonoidalClosed.comp W V U) ≫
          comparison W U =
      (comparison V U ⊗ₘ comparison W V) ≫
        (β_ ((ihom (right.obj V)).obj (right.obj U)) ((ihom (right.obj W)).obj (right.obj V))).hom ≫
          MonoidalClosed.comp (right.obj W) (right.obj V) (right.obj U) := by
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← rightMu, Functor.LaxBraided.braided_assoc, rightMu, comparison_composition,
    ← BraidedCategory.braiding_naturality_assoc]

end SimplicialSpace.FirstProjection
