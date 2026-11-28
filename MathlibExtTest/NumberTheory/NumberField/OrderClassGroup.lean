/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.OrderClassGroup

/-!
# Tests for the map of class groups of an order
-/

set_option autoImplicit false

@[expose] public section

namespace OrderClassGroupTest

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}

/-- The map of class groups sends the class of an invertible integral ideal `𝔟` to that of
`𝔟𝒪_K`. -/
example [IsFractionRing O K] (hO : NumberField.IsOrder K O) (b : Ideal O)
    (hb : IsUnit (b : FractionalIdeal O⁰ K)) :
    NumberField.IsOrder.classGroupMap hO (ClassGroup.mk K hb.unit) =
      ClassGroup.mk K (Units.map hO.extendFractionalIdeal.toMonoidHom hb.unit) :=
  NumberField.IsOrder.classGroupMap_mk hO _

example [IsFractionRing O K] (hO : NumberField.IsOrder K O) (b : Ideal O) :
    hO.extendFractionalIdeal (b : FractionalIdeal O⁰ K) =
      ((b.map (Subalgebra.inclusion hO.le_integralClosure) : Ideal (integralClosure ℤ K)) :
        FractionalIdeal (integralClosure ℤ K)⁰ K) :=
  hO.extendFractionalIdeal_coeIdeal b

#check @NumberField.IsOrder.classGroupMap
#check @NumberField.IsOrder.extendFractionalIdeal_spanSingleton

end OrderClassGroupTest
