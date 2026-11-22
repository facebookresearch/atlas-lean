/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedOrdinaryHoProducts
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStableHoPreadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# The same original ordinary-Ho product is a biproduct

The original R-target product retains both original Ho projection maps.
The earned product lift supplies its two actual injections. The original
ordinary suspension equivalence earns the preadditive structure, so this
same fan and these same injections satisfy both universal properties.
The original caller zero and these binary products then supply finite
biproducts on the unchanged ordinary homotopy category.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits HomotopicalAlgebra
open scoped ZeroObject

namespace HomotopicalAlgebra.OrdinaryStableHoBiproducts

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)

include g in
/-- The SAME original caller zero gives the actual zero-object interface. -/
theorem hasZeroObject : HasZeroObject (HomotopyCategory C) :=
  (GeneratedOrdinaryHoZero.isZero g (0 : C) (isZero_zero C)).hasZeroObject

include g in
/-- The original caller zero and the original generated binary products give every finite product. -/
theorem hasFiniteProducts : HasFiniteProducts (HomotopyCategory C) := by
  let := hasZeroObject g
  let := GeneratedOrdinaryHoProducts.hasBinaryProducts g
  exact hasFiniteProducts_of_has_binary_and_terminal

variable [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

/-- Both injections are the original product lifts of the same identity and zero maps. -/
def bicone (Y Z : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    BinaryBicone Y Z := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact
    { pt := GeneratedOrdinaryHoProducts.product g Y Z
      fst := (GeneratedOrdinaryHoProducts.fan g Y Z).fst
      snd := (GeneratedOrdinaryHoProducts.fan g Y Z).snd
      inl := GeneratedOrdinaryHoProducts.lift g (𝟙 Y) 0
      inr := GeneratedOrdinaryHoProducts.lift g 0 (𝟙 Z)
      inl_fst := GeneratedOrdinaryHoProducts.lift_fst g _ _
      inl_snd := GeneratedOrdinaryHoProducts.lift_snd g _ _
      inr_fst := GeneratedOrdinaryHoProducts.lift_fst g _ _
      inr_snd := GeneratedOrdinaryHoProducts.lift_snd g _ _ }

/-- The SAME actual original fan and its two actual injections give both universal properties. -/
def isBilimit (Y Z : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (bicone g Y Z).IsBilimit := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact isBinaryBilimitOfIsLimit _ (GeneratedOrdinaryHoProducts.isLimitFan g Y Z)

/-- The actual identity of the original product is the sum of its two original projector words. -/
theorem total (Y Z : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (bicone g Y Z).fst ≫ (bicone g Y Z).inl +
      (bicone g Y Z).snd ≫ (bicone g Y Z).inr = 𝟙 (GeneratedOrdinaryHoProducts.product g Y Z) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact CategoryTheory.Limits.IsBilimit.binary_total (isBilimit g Y Z)

/-- The original coproduct desc retains both actual product projections and both caller maps. -/
def desc {Y Z T : HomotopyCategory C} (f : Y ⟶ T) (h : Z ⟶ T) :
    GeneratedOrdinaryHoProducts.product g Y Z ⟶ T := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact (bicone g Y Z).fst ≫ f + (bicone g Y Z).snd ≫ h

/-- The first original injection reads back the entire first caller map. -/
theorem inl_desc {Y Z T : HomotopyCategory C} (f : Y ⟶ T) (h : Z ⟶ T) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (bicone g Y Z).inl ≫ desc g f h = f := by
  let := OrdinaryStableHoPreadditive.preadditive g
  simp only [desc, Preadditive.comp_add, ← Category.assoc, BinaryBicone.inl_fst,
    BinaryBicone.inl_snd, Category.id_comp, zero_comp, add_zero]

/-- The second original injection reads back the entire second caller map. -/
theorem inr_desc {Y Z T : HomotopyCategory C} (f : Y ⟶ T) (h : Z ⟶ T) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (bicone g Y Z).inr ≫ desc g f h = h := by
  let := OrdinaryStableHoPreadditive.preadditive g
  simp only [desc, Preadditive.comp_add, ← Category.assoc, BinaryBicone.inr_fst,
    BinaryBicone.inr_snd, Category.id_comp, zero_comp, zero_add]

/-- Both original injection composites jointly determine every original coproduct map. -/
theorem desc_unique {Y Z T : HomotopyCategory C}
    (f : Y ⟶ T) (h : Z ⟶ T) (m : GeneratedOrdinaryHoProducts.product g Y Z ⟶ T) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (bicone g Y Z).inl ≫ m = f → (bicone g Y Z).inr ≫ m = h → m = desc g f h := by
  let := OrdinaryStableHoPreadditive.preadditive g
  intro hm₁ hm₂
  apply BinaryCofan.IsColimit.hom_ext (isBilimit g Y Z).isColimit
  · exact hm₁.trans (inl_desc g f h).symm
  · exact hm₂.trans (inr_desc g f h).symm

/-- Every pair's original R product, projection maps and injections supply a genuine binary biproduct. -/
theorem hasBinaryBiproduct (Y Z : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    HasBinaryBiproduct Y Z := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact HasBinaryBiproduct.mk ⟨bicone g Y Z, isBilimit g Y Z⟩

/-- The actual original pair constructions give the full binary-biproduct existence interface. -/
theorem hasBinaryBiproducts :
    letI := OrdinaryStableHoPreadditive.preadditive g
    HasBinaryBiproducts (HomotopyCategory C) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact ⟨hasBinaryBiproduct g⟩

/-- Every specified finite family has a biproduct from its SAME actual finite product. -/
theorem hasFiniteBiproducts :
    letI := OrdinaryStableHoPreadditive.preadditive g
    HasFiniteBiproducts (HomotopyCategory C) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  let := hasFiniteProducts g
  exact HasFiniteBiproducts.of_hasFiniteProducts

end HomotopicalAlgebra.OrdinaryStableHoBiproducts
