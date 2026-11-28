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

/-- The ring of integers of `ℚ`, as an order of `ℚ`: every class has a representative prime to
`2`. -/
example (x : ClassGroup (integralClosure ℤ ℚ)) :
    ∃ (b : Ideal (integralClosure ℤ ℚ))
      (hb : IsUnit (b : FractionalIdeal (integralClosure ℤ ℚ)⁰ ℚ)),
        b ⊔ Ideal.span {2} = ⊤ ∧ ClassGroup.mk ℚ hb.unit = x :=
  (NumberField.isOrder_integralClosure ℚ).exists_isUnit_coeIdeal_sup_eq_top
    (by simp) x

/-- The class group map of the maximal order of `ℚ(ζ₃)` to itself is surjective. -/
example : Function.Surjective (ClassGroup.map
    (Subalgebra.inclusion (le_refl (integralClosure ℤ (CyclotomicField 3 ℚ)))).toRingHom
    (Subalgebra.inclusion_injective _)) :=
  NumberField.IsOrder.classGroup_map_surjective
    (NumberField.isOrder_integralClosure (CyclotomicField 3 ℚ))

/-- The conductor of the maximal order of `ℚ(ζ₃)` is nonzero. -/
example : ((integralClosure ℤ (CyclotomicField 3 ℚ)).comap
    (integralClosure ℤ (CyclotomicField 3 ℚ)).val).conductorIdeal ≠ ⊥ :=
  (NumberField.isOrder_integralClosure (CyclotomicField 3 ℚ)).conductorIdeal_ne_bot

variable {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}

/-- Every class of `Cl(𝒪_K)` comes from a class of an order `O`. -/
example (hO : NumberField.IsOrder K O) (y : ClassGroup (integralClosure ℤ K)) :
    ∃ x : ClassGroup O, ClassGroup.map (Subalgebra.inclusion hO.le_integralClosure).toRingHom
      (Subalgebra.inclusion_injective hO.le_integralClosure) x = y :=
  NumberField.IsOrder.classGroup_map_surjective hO y

/-- Every class of `Cl(𝒪_K)` has an invertible integral representative prime to the conductor
of an order `O`. -/
example (hO : NumberField.IsOrder K O) (y : ClassGroup (integralClosure ℤ K)) :
    ∃ (a : Ideal (integralClosure ℤ K))
      (ha : IsUnit (a : FractionalIdeal (integralClosure ℤ K)⁰ K)),
        a ⊔ (O.comap (integralClosure ℤ K).val).conductorIdeal = ⊤ ∧ ClassGroup.mk K ha.unit = y :=
  ClassGroup.exists_isUnit_coeIdeal_sup_eq_top K hO.conductorIdeal_ne_bot y

#check @NumberField.IsOrder.conductorIdeal_ne_bot
#check @NumberField.IsOrder.exists_isUnit_coeIdeal_sup_eq_top
#check @NumberField.IsOrder.classGroup_map_surjective

end OrderClassGroupSurjectiveTest
