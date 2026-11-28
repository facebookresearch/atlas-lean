/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.ClassGroup.CoprimeInvertibleRepresentative
public import Mathlib.RingTheory.Int.Basic

/-!
# Tests for invertible ideal-class representatives coprime to a given ideal
-/

set_option autoImplicit false

@[expose] public section

namespace CoprimeInvertibleRepresentativeTest

open scoped nonZeroDivisors

/-- Every class of `Cl(ℤ)` has an invertible integral representative prime to `6`. -/
example (x : ClassGroup ℤ) :
    ∃ (b : Ideal ℤ) (hb : IsUnit (b : FractionalIdeal ℤ⁰ ℚ)), b ⊔ Ideal.span {6} = ⊤ ∧
      ClassGroup.mk ℚ hb.unit = x :=
  ClassGroup.exists_isUnit_coeIdeal_sup_eq_top ℚ (by simp) x

/-- In a Dedekind domain, with any fraction field, every class has an invertible integral
representative coprime to a given nonzero ideal. -/
example {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] (a : Ideal A) (ha : a ≠ ⊥) (x : ClassGroup A) :
    ∃ (b : Ideal A) (hb : IsUnit (b : FractionalIdeal A⁰ K)), b ⊔ a = ⊤ ∧
      ClassGroup.mk K hb.unit = x :=
  ClassGroup.exists_isUnit_coeIdeal_sup_eq_top K ha x

#check @ClassGroup.exists_isUnit_coeIdeal_sup_eq_top

end CoprimeInvertibleRepresentativeTest
