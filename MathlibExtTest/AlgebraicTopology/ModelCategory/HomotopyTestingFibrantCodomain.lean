/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingFibrantCodomain
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneSystem
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFactorization

/-!
# Public square and terminal-map consumers of testing right lifting
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe w v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.HomotopyTestingFibrantCodomain

section Generic

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
  [HasTerminal C] (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
  (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An]

/-- Global inclusion gives an actual An-square lift at an arbitrary codomain,
with no initial-object, factorization or object-fibrancy hypotheses. -/
theorem anodyneSquare {A B X Y : C} (p : X ⟶ Y)
    (hp : P.testingFibrations An p) (i : A ⟶ B) (hi : An i)
    (a : A ⟶ X) (b : B ⟶ Y) (sq : CommSq a i p b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  have hNF := Precylinder.IsAnodyneSystem.testingFibrations_le_naiveFibrations P An p hp
  have : HasLiftingProperty i p := hNF i hi
  have : sq.HasLift := inferInstance
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end Generic

open SSet SSet.joyalInterval

local instance : MorphismProperty.HasFactorization auxiliaryAnodyneExtensions.{u}
    auxiliaryAnodyneExtensions.rlp := by
  change MorphismProperty.HasFactorization auxiliaryAnodyneExtensions.{u}
    auxiliaryNaiveFibrations.{u}
  infer_instance

/-- A finite-J naive fibration with naive codomain lifts every original
monic testing map, retaining both prescribed diagonal equations. -/
theorem finiteJTestingSquare {A B X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : auxiliaryNaiveFibrations p) (hY : auxiliaryNaiveFibrantObjects Y)
    (i : A ⟶ B) [Mono i]
    (hi : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions i)
    (a : A ⟶ X) (b : B ⟶ Y) (sq : CommSq a i p b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  have hF :=
    (Precylinder.IsAnodyneSystem.testingFibrations_iff_naiveFibrations_of_naiveFibrant
      productPrecylinder auxiliaryAnodyneExtensions p hY).mpr hp
  have : HasLiftingProperty i p := hF i ⟨inferInstance, hi⟩
  have : sq.HasLift := inferInstance
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- The reverse finite-J iff gives the actual naive map and derives naive
source fibrancy through terminal composition, without assuming it. -/
theorem finiteJNaiveSource {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : productPrecylinder.testingFibrations auxiliaryAnodyneExtensions p)
    (hY : auxiliaryNaiveFibrantObjects Y) :
    auxiliaryNaiveFibrations p ∧ auxiliaryNaiveFibrantObjects X := by
  have hNF :=
    (Precylinder.IsAnodyneSystem.testingFibrations_iff_naiveFibrations_of_naiveFibrant
      productPrecylinder auxiliaryAnodyneExtensions p hY).mp hp
  refine ⟨hNF, ?_⟩
  change auxiliaryAnodyneExtensions.rlp (terminal.from X)
  change auxiliaryAnodyneExtensions.rlp p at hNF
  change auxiliaryAnodyneExtensions.rlp (terminal.from Y) at hY
  simpa only [terminal.comp_from] using
    auxiliaryAnodyneExtensions.rlp.comp_mem p (terminal.from Y) hNF hY

end MathlibExtTest.AlgebraicTopology.ModelCategory.HomotopyTestingFibrantCodomain
