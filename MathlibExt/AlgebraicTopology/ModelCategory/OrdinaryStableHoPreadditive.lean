/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStableHoGroups
import MathlibExt.CategoryTheory.Preadditive.GroupConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedOrdinaryHoZero

/-!
# The original ordinary stable Ho is preadditive

The commutative Hom groups were constructed from the original framing
and its same ordinary counit. Their original multiplication, identity
and inverse are now written additively. Both earned original composition
group maps prove bilinearity on the unchanged homotopy-category carrier.
No preadditive or Hom-group conclusion is supplied as a premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits HomotopicalAlgebra
open scoped ZeroObject

namespace HomotopicalAlgebra.OrdinaryStableHoPreadditive

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

/-- The original constructed Hom groups give additive commutative groups on the SAME actual Hom types. -/
@[instance_reducible]
def homGroup (X Y : HomotopyCategory C) : AddCommGroup (X ⟶ Y) :=
  @Additive.addCommGroup _ (OrdinaryStableHoGroups.commGroup g X Y)

/-- Both original Ho composition functions are linear for the SAME actual constructed Hom operations. -/
@[instance_reducible]
def preadditive : Preadditive (HomotopyCategory C) :=
  Preadditive.ofHomGroups (OrdinaryStableHoGroups.group g) (OrdinaryStableHoGroups.mul_comm g)
    (fun X _Y _Z h => OrdinaryStableHoGroups.postcompose g X h)
    (fun X _Y _Z h f => OrdinaryStableHoGroups.postcompose_apply g X h f)
    (fun _X _Y Z f => OrdinaryStableHoGroups.precompose g f Z)
    (fun _X _Y Z f h => OrdinaryStableHoGroups.precompose_apply g f Z h)

/-- Every Hom group field is the SAME actual constructed additive group. -/
theorem preadditive_homGroup (X Y : HomotopyCategory C) :
    (preadditive g).homGroup X Y = homGroup g X Y := rfl

/-- The actual caller zero maps give the SAME additive zero class in the original ordinary Ho. -/
theorem map_nullMap_eq_zero (Z : C) (hZ : IsZero Z) (X Y : C) :
    letI := preadditive g
    (toHomotopyCategory C).map (OrdinaryHoChosenPuppe.nullMap Z hZ X Y) = 0 := by
  let := preadditive g
  have hz : IsZero ((toHomotopyCategory C).obj Z) := GeneratedOrdinaryHoZero.isZero g Z hZ
  rw [OrdinaryHoChosenPuppe.nullMap, Functor.map_comp]
  have hn : (toHomotopyCategory C).map (OrdinaryHoChosenPuppe.fromZero Z hZ Y) = 0 :=
    hz.eq_of_src _ _
  rw [hn, comp_zero]

/-- The original ordinary cofiber null class is exactly the SAME constructed additive zero. -/
theorem nullHom_eq_zero (X Y : C) :
    letI := preadditive g
    OrdinaryHoCofiberKernel.nullHom X Y = 0 := by
  let := preadditive g
  change (toHomotopyCategory C).map
    (OrdinaryHoChosenPuppe.nullMap (0 : C) (isZero_zero C) X Y) = 0
  exact map_nullMap_eq_zero g (0 : C) (isZero_zero C) X Y

end HomotopicalAlgebra.OrdinaryStableHoPreadditive
