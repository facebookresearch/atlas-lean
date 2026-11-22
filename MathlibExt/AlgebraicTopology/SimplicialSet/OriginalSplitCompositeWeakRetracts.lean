/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Realization weakness of the original maps in a split composite.
import Mathlib.CategoryTheory.MorphismProperty.Retract
import MathlibExt.CategoryTheory.Retract
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence

/-!
# Weak equivalences from split composites

If `u : A ⟶ B` and `v : B ⟶ A` satisfy `v ≫ u = 𝟙 B`, realization weakness of `u ≫ v` implies realization weakness of both `u` and `v`. Each conclusion follows from the corresponding strict retract of the full composite arrow.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory

namespace SSet

/-- Actual scalar realization weakness descends to u by its complete strict Arrow retract. -/
theorem realizationWeak_of_splitComposite_left {A B : SSet.{u}}
    (u : A ⟶ B) (v : B ⟶ A) (h : v ≫ u = 𝟙 B)
    (hw : realizationWeakEquivalences (u ≫ v)) : realizationWeakEquivalences u :=
  realizationWeakEquivalences.of_retract (splitCompositeLeftRetract u v h) hw

/-- The same scalar composite proof also gives v, without comparison-fibration or endpoint-Kan
input. -/
theorem realizationWeak_of_splitComposite_right {A B : SSet.{u}}
    (u : A ⟶ B) (v : B ⟶ A) (h : v ≫ u = 𝟙 B)
    (hw : realizationWeakEquivalences (u ≫ v)) : realizationWeakEquivalences v :=
  realizationWeakEquivalences.of_retract (splitCompositeRightRetract u v h) hw

end SSet
