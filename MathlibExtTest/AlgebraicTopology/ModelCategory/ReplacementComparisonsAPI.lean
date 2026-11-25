/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import MathlibExt.AlgebraicTopology.ModelCategory.StructuredReplacementComparisons

/-!
# Public replacement comparison integration

Two independently supplied generation choices retain their own Q/R maps and
weak comparison legs. Four supplied factor records construct the structured
comparison package; the tests use its whole natural transformations and
localization maps, without assuming a comparison package as input.

An arbitrary `GeneratedFunctorialReplacements.Data` supplies the stated
replacement properties. Its independent factor fields need not construct its
Q/R fields. The factory and generation constructors provide that coupling.
-/

noncomputable section

universe w₁ w₂ uC vC uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra

namespace MathlibExtTest.ReplacementComparisonsAPI

section GeneratedChoices

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ₁ : Cardinal.{w₁}} [Fact κ₁.IsRegular] [OrderBot κ₁.ord.ToType]
  {κ₂ : Cardinal.{w₂}} [Fact κ₂.IsRegular] [OrderBot κ₂.ord.ToType]
  (d : CofibrantGenerationData C κ₁) (e : CofibrantGenerationData C κ₂)

open GeneratedFunctorialReplacements

example (X : C) :
    WeakEquivalence ((qComparisonLeft d e).app X) ∧
      WeakEquivalence ((qComparisonRight d e).app X) := by
  exact ⟨(weakEquivalence_iff _).mpr (Q_comparison_left_weak d e X),
    (weakEquivalence_iff _).mpr (Q_comparison_right_weak d e X)⟩

example (X : C) :
    WeakEquivalence ((rComparisonLeft d e).app X) ∧
      WeakEquivalence ((rComparisonRight d e).app X) := by
  exact ⟨(weakEquivalence_iff _).mpr (R_comparison_left_weak d e X),
    (weakEquivalence_iff _).mpr (R_comparison_right_weak d e X)⟩

example : qComparisonLeft d e ≫ counit d = qComparisonRight d e ≫ counit e := by
  exact Q_comparison_counits d e

example : unit d ≫ rComparisonLeft d e = unit e ≫ rComparisonRight d e := by
  exact R_comparison_units d e

example {X Y : C} (f : X ⟶ Y) :
    (Q d ⋙ Q e).map f ≫ (qComparisonLeft d e).app Y ≫ (counit d).app Y =
      (qComparisonRight d e).app X ≫ (counit e).app X ≫ f := by
  calc
    (Q d ⋙ Q e).map f ≫ (qComparisonLeft d e).app Y ≫ (counit d).app Y =
        ((qComparisonLeft d e).app X ≫ (Q d).map f) ≫ (counit d).app Y := by
      rw [← Category.assoc, Q_comparison_left_naturality]
    _ = ((qComparisonLeft d e).app X ≫ (counit d).app X) ≫ f := by
      rw [Category.assoc, (counit d).naturality, Functor.id_map, ← Category.assoc]
    _ = (qComparisonRight d e).app X ≫ (counit e).app X ≫ f := by
      simpa only [NatTrans.comp_app, Category.assoc] using
        congrArg (fun t => t.app X ≫ f) (Q_comparison_counits d e)

example {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences C ((fromGeneration d).Q.map f) ∧
      weakEquivalences C ((fromGeneration e).R.map f) := by
  exact ⟨(fromGeneration d).q_map_weak f hf, (fromGeneration e).r_map_weak f hf⟩

end GeneratedChoices

section StructuredComparisons

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  (U : D ⥤ C)
  (FcC : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (FfC : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (FcD : FunctorialFactorizationData (cofibrations D) (trivialFibrations D))
  (FfD : FunctorialFactorizationData (trivialCofibrations D) (fibrations D))
  (hW : weakEquivalences D = (weakEquivalences C).inverseImage U)

open StructuredReplacementComparisons

local notation "qC" => GeneratedFunctorialReplacements.replacementsOfFactors FcC FfC
local notation "qD" => GeneratedFunctorialReplacements.replacementsOfFactors FcD FfD
local notation "πC" => CategoryTheory.MorphismProperty.Q (weakEquivalences C)
local notation "πD" => CategoryTheory.MorphismProperty.Q (weakEquivalences D)

example (X : D) :
    weakEquivalences C ((underlyingQCounit U FcD FfD).app X) ∧
      weakEquivalences C ((baseQCounit U FcC FfC).app X) := by
  exact ⟨underlyingQCounit_weak U FcD FfD hW X, baseQCounit_weak U FcC FfC X⟩

example (X : D) :
    weakEquivalences C ((fibrantZigzagLeft U FcC FfC FcD FfD).app X) ∧
      weakEquivalences C ((fibrantZigzagRight U FcC FfC FcD FfD).app X) := by
  exact ⟨fibrantZigzagLeft_weak U FcC FfC FcD FfD X,
    fibrantZigzagRight_weak U FcC FfC FcD FfD hW X⟩

example {X Y : D} (f : X ⟶ Y) :
    (((qD).Q ⋙ U) ⋙ πC).map f ≫
        (underlyingQComparisonIso U FcC FfC FcD FfD hW).hom.app Y =
      (underlyingQComparisonIso U FcC FfC FcD FfD hW).hom.app X ≫
        ((U ⋙ (qC).Q) ⋙ πC).map f := by
  exact (underlyingQComparisonIso U FcC FfC FcD FfD hW).hom.naturality f

example :
    (underlyingRComparisonIso U FcC FfC FcD FfD hW).hom ≫
        (underlyingRComparisonIso U FcC FfC FcD FfD hW).inv =
      𝟙 (((qD).R ⋙ U) ⋙ πC) := by
  exact (underlyingRComparisonIso U FcC FfC FcD FfD hW).hom_inv_id

example {X Y : D} (f : X ⟶ Y) :
    (localizedForgetful U hW).map ((πD).map f) = (πC).map (U.map f) := by
  exact localizedForgetful_map U hW f

variable {L : C ⥤ D} (adj : L ⊣ U)
  (hF : fibrations D = (fibrations C).inverseImage U)

example (X : D) :
    IsFibrant (U.obj ((qD).R.obj X)) := by
  exact underlyingR_fibrant U FcD FfD hW adj hF X

example {X Y : D} (f : X ⟶ Y) :
    (construct U FcC FfC FcD FfD hW adj hF).chosen.map ((πD).map f) =
      (πC).map (U.map ((construct U FcC FfC FcD FfD hW adj hF).structured.R.map f)) := by
  exact chosenRight_map U FcD FfD hW adj hF f

example :
    (construct U FcC FfC FcD FfD hW adj hF).qComparison.hom ≫
        (construct U FcC FfC FcD FfD hW adj hF).qComparison.inv =
      𝟙 (((construct U FcC FfC FcD FfD hW adj hF).structured.Q ⋙ U) ⋙ πC) := by
  exact (construct U FcC FfC FcD FfD hW adj hF).qComparison.hom_inv_id

example (X : D) :
    (derivedForgetfulIso U FcD FfD hW adj hF).hom.app ((πD).obj X) ≫
        (derivedForgetfulIso U FcD FfD hW adj hF).inv.app ((πD).obj X) =
      𝟙 ((localizedForgetful U hW).obj ((πD).obj X)) := by
  exact (derivedForgetfulIso U FcD FfD hW adj hF).hom_inv_id_app ((πD).obj X)

end StructuredComparisons

end MathlibExtTest.ReplacementComparisonsAPI
