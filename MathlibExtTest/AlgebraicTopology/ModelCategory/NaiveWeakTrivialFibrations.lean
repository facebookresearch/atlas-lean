/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.ModelCategory.NaiveWeakTrivialFibrations
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneSystem

/-!
# Public consumers of weak naive-fibration recognition
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open SSet SSet.joyalInterval

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.NaiveWeakTrivialFibrations

/-- Testing membership supplies an actual section and complete finite-J
homotopy over the base; naive fibrancy of the codomain is explicit. -/
theorem finiteJDualData {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : auxiliaryNaiveFibrations p) (hY : auxiliaryNaiveFibrantObjects Y)
    (hw : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions p) :
    ∃ (s : Y ⟶ X) (K : joyalInterval ⊗ X ⟶ X),
      s ≫ p = 𝟙 Y ∧ (productPrecylinder.app X).i₀ ≫ K = 𝟙 X ∧
        (productPrecylinder.app X).i₁ ≫ K = p ≫ s ∧
          K ≫ p = (productPrecylinder.app X).π ≫ p := by
  obtain ⟨D⟩ :=
    Precylinder.IsAnodyneSystem.exists_dualDeformationData_of_testingEquivalence_of_naiveFibration
      productPrecylinder auxiliaryAnodyneExtensions p hp hY hw
  exact ⟨D.section_, D.homotopy.h, D.section_comp, D.homotopy.h₀,
    D.homotopy.h₁, D.over_base⟩

/-- The forward iff gives both strict diagonals for any supplied mono
square over the same naive-fibrant codomain. -/
theorem finiteJStrictLift {A B X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : auxiliaryNaiveFibrations p) (hY : auxiliaryNaiveFibrantObjects Y)
    (hw : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions p)
    (i : A ⟶ B) [Mono i] (a : A ⟶ X) (b : B ⟶ Y) (sq : CommSq a i p b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  have ht :=
    (Precylinder.IsAnodyneSystem.testingEquivalences_iff_rlp_monomorphisms_of_naiveFibration
      productPrecylinder auxiliaryAnodyneExtensions p hp hY).mp hw
  have hip : HasLiftingProperty i p := ht i (by infer_instance)
  have : sq.HasLift := hip.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- The reverse iff returns the actual testing class for the specified
system, using the same explicit naive-fibrant-codomain hypothesis. -/
theorem finiteJTesting {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : auxiliaryNaiveFibrations p) (hY : auxiliaryNaiveFibrantObjects Y)
    (ht : (MorphismProperty.monomorphisms SSet).rlp p) :
    productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions p :=
  (Precylinder.IsAnodyneSystem.testingEquivalences_iff_rlp_monomorphisms_of_naiveFibration
    productPrecylinder auxiliaryAnodyneExtensions p hp hY).mpr ht

end MathlibExtTest.AlgebraicTopology.ModelCategory.NaiveWeakTrivialFibrations
