/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRecognition

/-!
# Tests for generated two-family model-category recognition
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open HomotopicalAlgebra

namespace MathlibExtTest.HomotopicalAlgebra.GeneratedRecognition

variable {C : Type u} [Category.{v} C]
variable (I J W : MorphismProperty C)

#check HomotopicalAlgebra.SmithModelStructureData.ofGenerators
#check HomotopicalAlgebra.SmithModelStructureData.modelCategory

section Data

variable [I.HasSmallObjectArgument.{w}]
variable [J.HasSmallObjectArgument.{w}]
variable (h₂ : W.HasTwoOutOfThreeProperty)
variable (hTF : I.rlp = J.rlp ⊓ W)
variable (hJ : J.rlp.llp ≤ W)

noncomputable example :
    HomotopicalAlgebra.SmithModelStructureData.{w} (C := C) I W :=
  HomotopicalAlgebra.SmithModelStructureData.ofGenerators
    I J W h₂ hTF hJ

example :
    (HomotopicalAlgebra.SmithModelStructureData.ofGenerators
      I J W h₂ hTF hJ).J = J :=
  rfl

example : J.HasSmallObjectArgument.{w} :=
  (HomotopicalAlgebra.SmithModelStructureData.ofGenerators
    I J W h₂ hTF hJ).J_smallObject

example : MorphismProperty.IsWeakFactorizationSystem
    I.rlp.llp I.rlp :=
  (HomotopicalAlgebra.SmithModelStructureData.ofGenerators
    I J W h₂ hTF hJ).cofibration_wfs

example : MorphismProperty.IsWeakFactorizationSystem
    J.rlp.llp J.rlp :=
  (HomotopicalAlgebra.SmithModelStructureData.ofGenerators
    I J W h₂ hTF hJ).trivialCofibration_wfs

example : J.rlp.llp = I.rlp.llp ⊓ W :=
  (HomotopicalAlgebra.SmithModelStructureData.ofGenerators
    I J W h₂ hTF hJ).trivialCofibrations_eq

example : J.rlp = (I.rlp.llp ⊓ W).rlp :=
  (HomotopicalAlgebra.SmithModelStructureData.ofGenerators
    I J W h₂ hTF hJ).fibrations_eq

example : J.rlp ⊓ W = I.rlp :=
  (HomotopicalAlgebra.SmithModelStructureData.ofGenerators
    I J W h₂ hTF hJ).trivialFibrations_eq

example : J.rlp.llp ≤ I.rlp.llp :=
  MorphismProperty.antitone_llp (hTF.le.trans inf_le_left)

end Data

section ModelCategory

variable [I.HasSmallObjectArgument.{w}]
variable [J.HasSmallObjectArgument.{w}]
variable [CategoryWithCofibrations C]
variable [CategoryWithFibrations C]
variable [CategoryWithWeakEquivalences C]
variable [HasFiniteLimits C]
variable [HasFiniteColimits C]
variable (h₂ : W.HasTwoOutOfThreeProperty)
variable (hTF : I.rlp = J.rlp ⊓ W)
variable (hJ : J.rlp.llp ≤ W)
variable (hCof : cofibrations C = I.rlp.llp)
variable (hFib : fibrations C = J.rlp)
variable (hW : weakEquivalences C = W)

/-- This client deliberately assumes no `W.IsStableUnderRetracts`: the model
category constructor derives weak retract closure from the two WFSs. -/
noncomputable example : ModelCategory C :=
  HomotopicalAlgebra.SmithModelStructureData.modelCategory
    (HomotopicalAlgebra.SmithModelStructureData.ofGenerators
      I J W h₂ hTF hJ)
    h₂ hCof hFib hW

example : True := by
  fail_if_success
    have _ : W.IsStableUnderRetracts := inferInstance
  trivial

end ModelCategory

section MissingISmallObject

variable [J.HasSmallObjectArgument.{w}]
variable (h₂ : W.HasTwoOutOfThreeProperty)
variable (hTF : I.rlp = J.rlp ⊓ W)
variable (hJ : J.rlp.llp ≤ W)

example : True := by
  fail_if_success
    exact (HomotopicalAlgebra.SmithModelStructureData.ofGenerators
      I J W h₂ hTF hJ :
        HomotopicalAlgebra.SmithModelStructureData.{w} (C := C) I W)
  trivial

end MissingISmallObject

section MissingJSmallObject

variable [I.HasSmallObjectArgument.{w}]
variable (h₂ : W.HasTwoOutOfThreeProperty)
variable (hTF : I.rlp = J.rlp ⊓ W)
variable (hJ : J.rlp.llp ≤ W)

example : True := by
  fail_if_success
    exact (HomotopicalAlgebra.SmithModelStructureData.ofGenerators
      I J W h₂ hTF hJ :
        HomotopicalAlgebra.SmithModelStructureData.{w} (C := C) I W)
  trivial

end MissingJSmallObject

section MissingExplicitInputs

variable [I.HasSmallObjectArgument.{w}]
variable [J.HasSmallObjectArgument.{w}]
variable (h₂ : W.HasTwoOutOfThreeProperty)
variable (hTF : I.rlp = J.rlp ⊓ W)
variable (hJ : J.rlp.llp ≤ W)

example : True := by
  fail_if_success
    exact (HomotopicalAlgebra.SmithModelStructureData.ofGenerators
      I J W hTF hJ :
        HomotopicalAlgebra.SmithModelStructureData.{w} (C := C) I W)
  fail_if_success
    exact (HomotopicalAlgebra.SmithModelStructureData.ofGenerators
      I J W h₂ hJ :
        HomotopicalAlgebra.SmithModelStructureData.{w} (C := C) I W)
  fail_if_success
    exact (HomotopicalAlgebra.SmithModelStructureData.ofGenerators
      I J W h₂ hTF :
        HomotopicalAlgebra.SmithModelStructureData.{w} (C := C) I W)
  trivial

end MissingExplicitInputs

section UniverseOne

variable {C₁ : Type 1} [Category.{0} C₁]
variable (I₁ J₁ W₁ : MorphismProperty C₁)
variable [I₁.HasSmallObjectArgument.{1}]
variable [J₁.HasSmallObjectArgument.{1}]

noncomputable example
    (h₂ : W₁.HasTwoOutOfThreeProperty)
    (hTF : I₁.rlp = J₁.rlp ⊓ W₁)
    (hJ : J₁.rlp.llp ≤ W₁) :
    HomotopicalAlgebra.SmithModelStructureData.{1} I₁ W₁ :=
  HomotopicalAlgebra.SmithModelStructureData.ofGenerators
    I₁ J₁ W₁ h₂ hTF hJ

end UniverseOne

section UniverseZero

variable {C₀ : Type} [Category C₀]
variable (I₀ J₀ W₀ : MorphismProperty C₀)
variable [I₀.HasSmallObjectArgument.{0}]
variable [J₀.HasSmallObjectArgument.{0}]

noncomputable example
    (h₂ : W₀.HasTwoOutOfThreeProperty)
    (hTF : I₀.rlp = J₀.rlp ⊓ W₀)
    (hJ : J₀.rlp.llp ≤ W₀) :
    HomotopicalAlgebra.SmithModelStructureData.{0} I₀ W₀ :=
  HomotopicalAlgebra.SmithModelStructureData.ofGenerators
    I₀ J₀ W₀ h₂ hTF hJ

end UniverseZero

end MathlibExtTest.HomotopicalAlgebra.GeneratedRecognition

#print axioms HomotopicalAlgebra.SmithModelStructureData.ofGenerators
#print axioms HomotopicalAlgebra.SmithModelStructureData.modelCategory
