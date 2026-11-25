/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.CyclotomicThreeUnramified

@[expose] public section

open scoped NumberField

/-- Consumer with the original binders: an extension of `ℚ(ζ₃)` unramified at
every maximal ideal has degree one over `ℚ(ζ₃)`. -/
private theorem exactSource
    {F : Type*} [Field F] [NumberField F] [Algebra (CyclotomicField 3 ℚ) F]
    (h : ∀ (P : Ideal (𝓞 F)) (_ : P.IsMaximal),
      Algebra.IsUnramifiedAt (𝓞 (CyclotomicField 3 ℚ)) P) :
    Module.finrank (CyclotomicField 3 ℚ) F = 1 :=
  NumberField.finrank_cyclotomicField_three_eq_one_of_forall_isUnramifiedAt h

/-- The base field itself, viewed as an extension of `ℚ(ζ₃)`, has degree one;
this is the degree the theorem forces in the unramified case. -/
example : Module.finrank (CyclotomicField 3 ℚ) (CyclotomicField 3 ℚ) = 1 :=
  Module.finrank_self _
