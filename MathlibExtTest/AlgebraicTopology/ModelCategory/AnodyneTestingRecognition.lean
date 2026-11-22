/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneTestingRecognition
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneSystem
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFactorization

/-!
# Public consumers of monic testing recognition
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe w v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.AnodyneTestingRecognition

section Generic

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
  [HasInitial C] [InitialMonoClass C] [HasTerminal C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
  (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An]
  [MorphismProperty.HasFactorization An An.rlp]

/-- Recognition gives a lift against every actual naive fibration, with
both strict diagonal equations and no naive-source assumption. -/
theorem liftOfTesting {A B X Y : C} (i : A ⟶ B) [Mono i]
    (hB : An.naiveFibrantObjects B) (hi : P.testingEquivalences An i)
    (p : X ⟶ Y) (hp : An.rlp p) (a : A ⟶ X) (b : B ⟶ Y) (sq : CommSq a i p b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  have hAn :=
    (Precylinder.IsAnodyneSystem.testingEquivalences_iff_anodyne_of_mono_of_naiveFibrant
      P An i hB).mp hi
  have hip : HasLiftingProperty i p := hp i hAn
  have : sq.HasLift := hip.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end Generic

open SSet SSet.joyalInterval

local instance : MorphismProperty.HasFactorization auxiliaryAnodyneExtensions.{u}
    auxiliaryAnodyneExtensions.rlp := by
  change MorphismProperty.HasFactorization auxiliaryAnodyneExtensions.{u}
    auxiliaryNaiveFibrations.{u}
  infer_instance

/-- The forward iff keeps the original monomorphism and actual naive
codomain for the finite-J class, without assuming the source naive. -/
theorem finiteJAnodyne {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    (hY : auxiliaryNaiveFibrantObjects Y)
    (hi : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions i) :
    auxiliaryAnodyneExtensions i :=
  (Precylinder.IsAnodyneSystem.testingEquivalences_iff_anodyne_of_mono_of_naiveFibrant
    productPrecylinder auxiliaryAnodyneExtensions i hY).mp hi

/-- The same public iff also supplies testing membership in the reverse
direction for the specified finite-J system. -/
theorem finiteJTesting {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    (hY : auxiliaryNaiveFibrantObjects Y) (hi : auxiliaryAnodyneExtensions i) :
    productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions i :=
  (Precylinder.IsAnodyneSystem.testingEquivalences_iff_anodyne_of_mono_of_naiveFibrant
    productPrecylinder auxiliaryAnodyneExtensions i hY).mpr hi

end MathlibExtTest.AlgebraicTopology.ModelCategory.AnodyneTestingRecognition
