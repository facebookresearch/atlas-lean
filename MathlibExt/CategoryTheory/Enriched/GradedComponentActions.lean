/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.GradeNaturality
public import MathlibExt.CategoryTheory.Enriched.GradedInputComposition

/-!
# Grade-first components and ordinary input actions

Postcomposition of a graded transformation acts by postcomposition on its
uncurried grade-first components.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

set_option maxHeartbeats 200000 in
-- Keep the original budget for the full graded component and closed Hom calculation.
/-- Ordinary postcomposition acts by postcomposition on every grade-first component. -/
theorem gradeFirstComponent_gradedPostcomp
    (Γ : Center V) {F G H : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (q : G ⟶ H) (a : A) :
    GradedNatTrans.gradeFirstComponent Γ (gradedPostcomp Γ t q) a =
      GradedNatTrans.gradeFirstComponent Γ t a ≫ component q a := by
  have hu := (congrArg MonoidalClosed.uncurry (gradedPostcomp_app Γ t q a)).trans
    (MonoidalClosed.uncurry_natural_right (t.app a) (component q a))
  exact (congrArg (fun p => (Γ.2.β (F.toEnrichedFunctor.obj a)).hom ≫ p) hu).trans
    (Category.assoc _ _ _).symm



/-- Ordinary precomposition acts by the original tensor source map
on every grade-first component. -/
theorem gradeFirstComponent_gradedPrecomp
    (Γ : Center V) {F' F G : EnrichedFunctorCat V A} (p : F' ⟶ F)
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (a : A) :
    GradedNatTrans.gradeFirstComponent Γ (gradedPrecomp Γ p t) a =
      (Γ.1 ◁ component p a) ≫ GradedNatTrans.gradeFirstComponent Γ t a := by
  dsimp only [GradedNatTrans.gradeFirstComponent]
  rw [gradedPrecomp_app, MonoidalClosed.uncurry_pre_app]
  simpa only [Category.assoc] using congrArg
    (fun q => q ≫ MonoidalClosed.uncurry (t.app a))
    (Γ.2.naturality (component p a)).symm

end CategoryTheory.EnrichedFunctorCat
