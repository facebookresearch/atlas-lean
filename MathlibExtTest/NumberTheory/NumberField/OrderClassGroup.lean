/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.OrderClassGroup

/-!
# Tests for the class group of an order and its map to the class group of the maximal order
-/

set_option autoImplicit false

@[expose] public section

namespace OrderClassGroupTest

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}

example : IsFractionRing (integralClosure ℤ K) K := inferInstance

example : IsDedekindDomain (integralClosure ℤ K) := inferInstance

/-- The map of class groups `ClassGroup.map` for the inclusion of an order sends the class of an
invertible integral ideal `𝔟` to that of `𝔟𝒪_K`. -/
example [IsFractionRing O K] (hO : NumberField.IsOrder K O) (b : Ideal O)
    (hb : IsUnit (b : FractionalIdeal O⁰ K))
    (hb' : IsUnit ((b.map (Subalgebra.inclusion hO.le_integralClosure) :
      Ideal (integralClosure ℤ K)) : FractionalIdeal (integralClosure ℤ K)⁰ K)) :
    ClassGroup.map (Subalgebra.inclusion hO.le_integralClosure).toRingHom
      (Subalgebra.inclusion_injective hO.le_integralClosure)
      (ClassGroup.mk K hb.unit) = ClassGroup.mk K hb'.unit := by
  rw [ClassGroup.map_mk K K]
  congr 1
  ext1
  rw [Units.coe_map, IsUnit.unit_spec, IsUnit.unit_spec]
  exact FractionalIdeal.extended_coeIdeal_eq_map _ _ _

#check @NumberField.instIsFractionRingIntegralClosure
#check @NumberField.instIsDedekindDomainIntegralClosure

end OrderClassGroupTest
