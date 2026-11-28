/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.OrderClassGroupSurjective
public import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Tests for ideal classes of an order prime to an ideal and surjectivity of `Cl(O) → Cl(𝒪_K)`
-/

set_option autoImplicit false

@[expose] public section

namespace OrderClassGroupSurjectiveTest

open scoped nonZeroDivisors

/-- Every class of `Cl(ℤ)` has an invertible integral representative prime to `6`. -/
example (x : ClassGroup ℤ) :
    ∃ (b : Ideal ℤ) (hb : IsUnit (b : FractionalIdeal ℤ⁰ ℚ)), b ⊔ Ideal.span {6} = ⊤ ∧
      ClassGroup.mk ℚ hb.unit = x :=
  ClassGroup.exists_isUnit_coeIdeal_sup_eq_top (by simp) x

/-- The ring of integers of `ℚ`, as an order of `ℚ`: every class has a representative prime to
`2`. -/
example (x : ClassGroup (integralClosure ℤ ℚ)) :
    ∃ (b : Ideal (integralClosure ℤ ℚ))
      (hb : IsUnit (b : FractionalIdeal (integralClosure ℤ ℚ)⁰ ℚ)),
        b ⊔ Ideal.span {2} = ⊤ ∧ ClassGroup.mk ℚ hb.unit = x :=
  (NumberField.isOrder_integralClosure ℚ).exists_isUnit_coeIdeal_sup_eq_top
    (by simp) x

/-- The class group map of the maximal order of `ℚ(ζ₃)` is surjective. -/
example : Function.Surjective (NumberField.IsOrder.classGroupMap
    (NumberField.isOrder_integralClosure (CyclotomicField 3 ℚ))) :=
  NumberField.IsOrder.classGroupMap_surjective _

/-- The conductor of the maximal order of `ℚ(ζ₃)` is nonzero. -/
example : ((integralClosure ℤ (CyclotomicField 3 ℚ)).comap
    (integralClosure ℤ (CyclotomicField 3 ℚ)).val).conductorIdeal ≠ ⊥ :=
  (NumberField.isOrder_integralClosure (CyclotomicField 3 ℚ)).conductorIdeal_ne_bot

variable {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K} [IsFractionRing O K]

/-- Every class of `Cl(𝒪_K)` comes from an invertible ideal of an order `O`. -/
example (hO : NumberField.IsOrder K O) (y : ClassGroup (integralClosure ℤ K)) :
    ∃ x : ClassGroup O, NumberField.IsOrder.classGroupMap hO x = y :=
  NumberField.IsOrder.classGroupMap_surjective hO y

#check @ClassGroup.exists_isUnit_coeIdeal_sup_eq_top
#check @NumberField.exists_isUnit_coeIdeal_sup_eq_top_integralClosure
#check @NumberField.IsOrder.conductorIdeal_ne_bot
#check @NumberField.IsOrder.exists_isUnit_coeIdeal_sup_eq_top
#check @NumberField.IsOrder.classGroupMap_surjective

end OrderClassGroupSurjectiveTest
