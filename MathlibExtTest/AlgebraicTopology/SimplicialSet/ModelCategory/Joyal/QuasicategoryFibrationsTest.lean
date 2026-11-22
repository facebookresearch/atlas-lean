/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.QuasicategoryFibrations

/-!
# Quasicategory Fibrations Test
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory MonoidalClosed Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.QuasicategoryFibrationsTest

variable {X Y : SSet.{u}} (p : X ⟶ Y) [SSet.Quasicategory Y]

/-- Codomain quasicategory suffices for the actual finite-J class bridge. -/
example : SSet.categoricalFibrations p ↔ SSet.joyalInterval.auxiliaryNaiveFibrations p :=
  SSet.joyalInterval.categoricalFibrations_iff_auxiliaryNaiveFibrations p

/-- The criterion needs no independently supplied source quasicategory. -/
example : SSet.categoricalFibrations p ↔
    SSet.InnerFibration p ∧ SSet.HasStrictEquivalenceLifting p :=
  SSet.categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting p

/-- The ordinary homotopy-category functor is the actual comparison target. -/
example : SSet.categoricalFibrations p ↔
    SSet.InnerFibration p ∧ (SSet.hoFunctor.map p).toFunctor.IsIsofibration :=
  SSet.categoricalFibrations_iff_innerFibration_and_hoIsofibration p

/-- The original coherent endpoint criterion is the actual lifting property. -/
example : SSet.categoricalFibrations p ↔ SSet.InnerFibration p ∧
    HasLiftingProperty SSet.coherentIso.endpointInclusion p :=
  SSet.categoricalFibrations_iff_innerFibration_and_coherentIsoEndpointLifting p

/-- The source criterion solves an arbitrary original weak-mono square,
retaining both original map equations. -/
example [SSet.InnerFibration p] [SSet.HasStrictEquivalenceLifting p]
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : SSet.categoricalEquivalences i) (a : A ⟶ X) (b : B ⟶ Y)
    (sq : CommSq a i p b) : ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  have hp : SSet.categoricalFibrations p :=
    (SSet.categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting p).mpr ⟨inferInstance, inferInstance⟩
  have hLP : HasLiftingProperty i p :=
    (SSet.categoricalFibrations.mem_iff p).mp hp i inferInstance hi
  let : sq.HasLift := hLP.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- The accepted native auxiliary class solves the original weak-mono square. -/
example (hp : SSet.joyalInterval.auxiliaryNaiveFibrations p)
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (hi : SSet.categoricalEquivalences i)
    (a : A ⟶ X) (b : B ⟶ Y) (sq : CommSq a i p b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  have h := (SSet.joyalInterval.categoricalFibrations_iff_auxiliaryNaiveFibrations p).mpr hp
  have hLP := (SSet.categoricalFibrations.mem_iff p).mp h i inferInstance hi
  let : sq.HasLift := hLP.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩


/-- The actual native naive right class has the same codomain-only criterion. -/
example : SSet.joyalInterval.auxiliaryNaiveFibrations p ↔
    SSet.InnerFibration p ∧ SSet.HasStrictEquivalenceLifting p :=
  SSet.joyalInterval.auxiliaryNaiveFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting p


end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.QuasicategoryFibrationsTest
