/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularPathDeckNaturality
import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedSpectralSequence

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u v

#check @CategoryTheory.regularPathInversePrecomposition_mul
#print axioms CategoryTheory.regularPathInversePrecomposition_mul
#check @SSet.KanComplex.nativeCoverSimplexPathGeneratorsEquiv_deck
#print axioms SSet.KanComplex.nativeCoverSimplexPathGeneratorsEquiv_deck
#check @TopCat.originalRegularRelativeChainIso_deck
#print axioms TopCat.originalRegularRelativeChainIso_deck
#check @TopCat.originalRegularRelativeChainComplex_eq_cokernel
#print axioms TopCat.originalRegularRelativeChainComplex_eq_cokernel
#check @TopCat.originalRegularRelativeChainProjection_eq_cokernelπ
#print axioms TopCat.originalRegularRelativeChainProjection_eq_cokernelπ
#check @TopCat.originalRegularRelativeChainProjection_epi
#print axioms TopCat.originalRegularRelativeChainProjection_epi
#check @TopCat.originalRegularRelativeHomologyIso_hom
#print axioms TopCat.originalRegularRelativeHomologyIso_hom
#check @SSet.KanComplex.nativeCoverDeckedSimplexLift_val
#print axioms SSet.KanComplex.nativeCoverDeckedSimplexLift_val

/-- Both object and Hom universes remain independent, and inverse
precomposition acts on every original path without a commutativity premise. -/
theorem client_original_groupoid_path_action {C : Type u} [Groupoid.{v} C]
    (y z : C) (a : End y) (γ : y ⟶ z) :
    (CategoryTheory.regularPathInversePrecomposition y a).app z (FreeAbelianGroup.of γ) =
      FreeAbelianGroup.of ((a⁻¹).asHom ≫ γ) :=
  CategoryTheory.regularPathInversePrecomposition_of y a z γ

/-- The two composable actions have the noncommutative LEFT product order
on the whole original coefficient natural transformation. -/
theorem client_entire_left_coefficient_product {C : Type u} [Groupoid.{v} C]
    (y : C) (a b : End y) :
    CategoryTheory.regularPathInversePrecomposition y (a*b) =
      CategoryTheory.regularPathInversePrecomposition y b ≫
        CategoryTheory.regularPathInversePrecomposition y a :=
  CategoryTheory.regularPathInversePrecomposition_mul y a b

/-- The actual original relative quotient commutes with the original
coefficient-induced chain map at the unchanged singular basepoint. -/
theorem client_original_cokernel_deck_projection {X Y : TopCat.{u}} (f : X ⟶ Y)
    (y : Y) (a : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm y))) :
    TopCat.originalRegularRelativeChainProjection f y ≫
        TopCat.originalRegularRelativeDeckChainMap f y a =
      TopCat.originalRegularDeckChainMap Y y a ≫
        TopCat.originalRegularRelativeChainProjection f y :=
  TopCat.originalRegularRelativeDeckChainMap_projection f y a

/-- The actual quotient, its epimorphy and homology map share the same original chain data. -/
theorem client_original_relative_computed_recipes {X Y : TopCat.{u}}
    (f : X ⟶ Y) [Mono f] (y : Y) (n : ℕ) :
    (TopCat.originalRegularRelativeChainProjection f y ≫
        (eqToIso (TopCat.originalRegularRelativeChainComplex_eq_cokernel f y)).hom =
      cokernel.π (TopCat.localCoefficientPullbackChainMap f
        (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)))) ∧
      Epi (TopCat.originalRegularRelativeChainProjection f y) ∧
      (TopCat.originalRegularRelativeHomologyIso f y n).hom =
        HomologicalComplex.homologyMap (TopCat.originalRegularRelativeChainIso f y).hom n := by
  exact ⟨TopCat.originalRegularRelativeChainProjection_eq_cokernelπ f y,
    TopCat.originalRegularRelativeChainProjection_epi f y,
    TopCat.originalRegularRelativeHomologyIso_hom f y n⟩

/-- The public lift value and its unchanged projection use the same whole selected simplex. -/
theorem client_native_decked_lift_value_and_projection {Y : SSet.{u}}
    (y : Y _⦋0⦌) (a : End (SSet.FundamentalGroupoid.mk y)) {n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ Y)
    (L : {L : (Δ[n] : SSet.{u}) ⟶ SSet.KanComplex.nativeCover Y y //
      L ≫ SSet.KanComplex.nativeCoverProjection Y y = σ}) :
    (SSet.KanComplex.nativeCoverDeckedSimplexLift y a σ L).val =
        L.val ≫ SSet.KanComplex.nativeCoverDeckMap a ∧
      (L.val ≫ SSet.KanComplex.nativeCoverDeckMap a) ≫
        SSet.KanComplex.nativeCoverProjection Y y = σ := by
  have h := SSet.KanComplex.nativeCoverDeckedSimplexLift_val y a σ L
  exact ⟨h, (congrArg (fun t => t ≫ SSet.KanComplex.nativeCoverProjection Y y) h.symm).trans
    (SSet.KanComplex.nativeCoverDeckedSimplexLift y a σ L).property⟩

end
