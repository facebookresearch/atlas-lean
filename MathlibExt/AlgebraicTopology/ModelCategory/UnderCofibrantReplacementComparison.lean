/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.Under
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Cofibrant under sources compared to trivial-fibration presentations

Cofibrancy in an under category means that its retained structure arrow is a
cofibration. The ordinary lifting axiom compares a cofibrant source to an
arbitrary trivial-fibration presentation over the same target. The comparison
preserves the carrier and is weak when the first source map is weak.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace HomotopicalAlgebra.UnderReplacementComparison

variable {C : Type u} [Category.{v} C] [ModelCategory C] {P : C}

/-- Under cofibrancy is exactly cofibrancy of the retained carrier arrow. -/
theorem isCofibrant_under_iff (X : Under P) : IsCofibrant X ↔ Cofibration X.hom := by
  rw [isCofibrant_iff_of_isInitial (Under.mkIdInitial.to X) Under.mkIdInitial,
    cofibrations_under_iff, Under.mkIdInitial_to_right]

/-- A cofibrant carrier and a cofibrant under object give a cofibrant underlying object. -/
theorem isCofibrant_right (X : Under P) [IsCofibrant P] [IsCofibrant X] :
    IsCofibrant X.right := by
  let _ : Cofibration X.hom := (isCofibrant_under_iff X).mp inferInstance
  exact isCofibrant_of_cofibration X.hom

variable {X X₁ X₂ : Under P} (q₁ : X₁ ⟶ X) (q₂ : X₂ ⟶ X)
  [IsCofibrant X₁] [Fibration q₂] [WeakEquivalence q₂]

/-- The actual model lift compares the cofibrant under source to a trivial-fibration presentation. -/
def comparison : X₁ ⟶ X₂ := by
  let sq : CommSq (initial.to X₂) (initial.to X₁) q₂ q₁ := ⟨initial.hom_ext _ _⟩
  exact sq.lift

/-- The comparison keeps the complete source-to-presentation triangle. -/
@[reassoc]
theorem comparison_fac : comparison q₁ q₂ ≫ q₂ = q₁ := by
  let sq : CommSq (initial.to X₂) (initial.to X₁) q₂ q₁ := ⟨initial.hom_ext _ _⟩
  exact sq.fac_right

/-- Its underlying arrow keeps the original carrier, rather than choosing another point. -/
@[reassoc]
theorem comparison_point : X₁.hom ≫ (comparison q₁ q₂).right = X₂.hom :=
  Under.w (comparison q₁ q₂)

/-- A weak map from the cofibrant source and the trivial-fibration presentation give a weak comparison. -/
theorem comparison_weak [WeakEquivalence q₁] : WeakEquivalence (comparison q₁ q₂) :=
  weakEquivalence_of_postcomp_of_fac (comparison_fac q₁ q₂)

/-- The forgetful model structure preserves the same weak comparison arrow. -/
theorem comparison_right_weak [WeakEquivalence q₁] :
    WeakEquivalence (comparison q₁ q₂).right := by
  let _ : WeakEquivalence (comparison q₁ q₂) := comparison_weak q₁ q₂
  infer_instance

end HomotopicalAlgebra.UnderReplacementComparison
