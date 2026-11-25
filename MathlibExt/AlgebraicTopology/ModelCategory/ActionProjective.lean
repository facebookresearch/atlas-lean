/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective
import Mathlib.AlgebraicTopology.ModelCategory.Transport
import Mathlib.CategoryTheory.Action.Limits

/-!
# Projective models on monoid actions

The actual action/functor-category equivalence transports the ordinary
projective model constructed from the original coefficient generators.
The source cardinal, ordinal bottom and complete underlying weak and
fibration classes are retained for every small monoid action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ u₁ w

namespace HomotopicalAlgebra.ActionProjective

open CategoryTheory MorphismProperty

section Factory

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (G : Type) [Monoid G]

/-- The actual ordinary projective action model at the original source cardinal. -/
@[instance_reducible]
noncomputable def modelCategory : ModelCategory (Action C G) := by
  let e := Action.functorCategoryEquivalence C G
  letI : ModelCategory (SingleObj G ⥤ C) :=
    FunctorProjective.modelCategory.{w, 0, 0, u₁, v₁} (J := SingleObj G) d
  letI : CategoryWithCofibrations (Action C G) :=
    ⟨(cofibrations (SingleObj G ⥤ C)).inverseImage e.functor⟩
  letI : CategoryWithFibrations (Action C G) :=
    ⟨(fibrations (SingleObj G ⥤ C)).inverseImage e.functor⟩
  letI : CategoryWithWeakEquivalences (Action C G) :=
    ⟨(weakEquivalences (SingleObj G ⥤ C)).inverseImage e.functor⟩
  exact ModelCategory.transport e rfl rfl rfl

/-- The actual projective action model creates precisely the original coefficient weak class. -/
theorem weakEquivalences_eq :
    letI := modelCategory d G
    weakEquivalences (Action C G) =
      (weakEquivalences C).inverseImage (Action.forget C G) := by
  let _ := modelCategory d G
  let _ : ModelCategory (SingleObj G ⥤ C) :=
    FunctorProjective.modelCategory.{w, 0, 0, u₁, v₁} (J := SingleObj G) d
  change (weakEquivalences (SingleObj G ⥤ C)).inverseImage
    (Action.functorCategoryEquivalence C G).functor = _
  rw [FunctorProjective.weakEquivalences_eq.{w, 0, 0, u₁, v₁} d]
  ext A B f
  change (∀ _ : SingleObj G, weakEquivalences C f.hom) ↔ weakEquivalences C f.hom
  exact ⟨fun h => h (SingleObj.star _), fun h _ => h⟩

/-- The actual projective action model creates precisely the original coefficient fibration
class. -/
theorem fibrations_eq :
    letI := modelCategory d G
    fibrations (Action C G) = (fibrations C).inverseImage (Action.forget C G) := by
  let _ := modelCategory d G
  let _ : ModelCategory (SingleObj G ⥤ C) :=
    FunctorProjective.modelCategory.{w, 0, 0, u₁, v₁} (J := SingleObj G) d
  change (fibrations (SingleObj G ⥤ C)).inverseImage
    (Action.functorCategoryEquivalence C G).functor = _
  rw [FunctorProjective.fibrations_eq.{w, 0, 0, u₁, v₁} d]
  ext A B f
  change (∀ _ : SingleObj G, fibrations C f.hom) ↔ fibrations C f.hom
  exact ⟨fun h => h (SingleObj.star _), fun h _ => h⟩

/-- Both created classes retain their complete ordinary trivial-fibration intersection. -/
theorem trivialFibrations_eq :
    letI := modelCategory d G
    trivialFibrations (Action C G) =
      (trivialFibrations C).inverseImage (Action.forget C G) := by
  let _ := modelCategory d G
  change fibrations (Action C G) ⊓ weakEquivalences (Action C G) = _
  rw [fibrations_eq d G, weakEquivalences_eq d G]
  rfl

end Factory

end HomotopicalAlgebra.ActionProjective
