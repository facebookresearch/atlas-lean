/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStableHoBiproducts
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Additivity of the actual ordinary suspension and loop adjunction

The original generated binary products, the earned ordinary-Ho Hom groups
and the actual framing adjunction prove additivity of both functors.
The resulting additive Hom equivalence has the same full functions,
unit, counit and naturality squares as that original ordinary adjunction.
The specified ordinary suspension equivalence supplies the actual loop
inverse and both original adjunction isomorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryStableHoAdditive

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

local notation "Σ" => DerivedSuspensionLoopAdjunction.suspension
  (GeneratedFunctorialReplacements.fromGeneration g)
local notation "Ω" => DerivedSuspensionLoopAdjunction.loops
  (GeneratedFunctorialReplacements.fromGeneration g)
local notation "adjOrd" => DerivedSuspensionLoopAdjunction.adjunction
  (GeneratedFunctorialReplacements.fromGeneration g)

/-- The actual ordinary right adjunction and earned original products prove loop additivity. -/
theorem loops_additive :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (Ω).Additive := by
  let := OrdinaryStableHoPreadditive.preadditive g
  let := GeneratedOrdinaryHoProducts.hasBinaryProducts g
  let : (Ω).IsRightAdjoint := (adjOrd).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products Ω

/-- The SAME actual ordinary adjunction proves suspension additivity from its earned additive right functor. -/
theorem suspension_additive :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (Σ).Additive := by
  let := OrdinaryStableHoPreadditive.preadditive g
  let := loops_additive g
  exact (adjOrd).left_adjoint_additive

/-- The genuine ordinary Hom equivalence is additive for the SAME constructed Hom operations. -/
def homAddEquiv (X Y : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    ((Σ).obj X ⟶ Y) ≃+ (X ⟶ (Ω).obj Y) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  let := suspension_additive g
  exact (adjOrd).homAddEquiv X Y

/-- Its entire forward function is the original framing ordinary Hom function. -/
theorem homAddEquiv_apply (X Y : HomotopyCategory C) (f : (Σ).obj X ⟶ Y) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    homAddEquiv g X Y f = (adjOrd).homEquiv X Y f := rfl

/-- Its entire inverse function is the same original ordinary Hom inverse. -/
theorem homAddEquiv_symm_apply (X Y : HomotopyCategory C) (f : X ⟶ (Ω).obj Y) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (homAddEquiv g X Y).symm f = ((adjOrd).homEquiv X Y).symm f := rfl

/-- Both original source functions retain their full original Hom naturality square. -/
theorem homAddEquiv_source {X X' : HomotopyCategory C} (f : X ⟶ X')
    (Y : HomotopyCategory C) (h : (Σ).obj X' ⟶ Y) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    homAddEquiv g X Y ((Σ).map f ≫ h) = f ≫ homAddEquiv g X' Y h := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact (adjOrd).homEquiv_naturality_left f h

/-- Both original target functions retain their full original Hom naturality square. -/
theorem homAddEquiv_target (X : HomotopyCategory C) {Y Y' : HomotopyCategory C}
    (f : Y ⟶ Y') (h : (Σ).obj X ⟶ Y) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    homAddEquiv g X Y' (h ≫ f) = homAddEquiv g X Y h ≫ (Ω).map f := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact (adjOrd).homEquiv_naturality_right h f

/-- The same actual ordinary unit is the complete additive Hom forward comparison word. -/
theorem homAddEquiv_unit (X Y : HomotopyCategory C) (f : (Σ).obj X ⟶ Y) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    homAddEquiv g X Y f = (adjOrd).unit.app X ≫ (Ω).map f := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact (adjOrd).homEquiv_unit X Y f

/-- The same actual ordinary counit is the complete additive Hom inverse comparison word. -/
theorem homAddEquiv_counit (X Y : HomotopyCategory C) (f : X ⟶ (Ω).obj Y) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (homAddEquiv g X Y).symm f = (Σ).map f ≫ (adjOrd).counit.app Y := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact (adjOrd).homEquiv_counit X Y f

/-- The specified original ordinary suspension equivalence makes its SAME actual loop right adjoint an inverse. -/
theorem loops_isEquivalence : (Ω).IsEquivalence :=
  (adjOrd).isEquivalence_right_of_isEquivalence_left

/-- The ordinary equivalence retains the actual framing suspension, actual loops, original unit and counit. -/
def equivalence : HomotopyCategory C ≌ HomotopyCategory C :=
  (adjOrd).toEquivalence

/-- Both original unit comparison functions are retained on every original Ho object. -/
theorem equivalence_unit (X : HomotopyCategory C) :
    (equivalence g).unitIso.hom.app X = (adjOrd).unit.app X := rfl

/-- Both original counit comparison functions are retained on every original Ho object. -/
theorem equivalence_counit (X : HomotopyCategory C) :
    (equivalence g).counitIso.hom.app X = (adjOrd).counit.app X := rfl

end HomotopicalAlgebra.OrdinaryStableHoAdditive
