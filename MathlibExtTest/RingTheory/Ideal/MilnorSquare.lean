/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Ideal.MilnorSquare

/-! # Consumers for the Milnor square of disjoint ideals -/

namespace IdealMilnorSquareTest

/-- The exact source statement (which fixed universe 0), with no added
hypothesis. -/
public theorem exactSource (A : Type) [CommRing A] (I₁ I₂ : Ideal A)
    (h : I₁ ⊓ I₂ = ⊥) :
    Function.Injective
        (fun a : A => (Ideal.Quotient.mk I₁ a, Ideal.Quotient.mk I₂ a)) ∧
    ∀ (x₁ : A ⧸ I₁) (x₂ : A ⧸ I₂),
      Ideal.Quotient.factor (le_sup_left : I₁ ≤ I₁ ⊔ I₂) x₁ =
        Ideal.Quotient.factor (le_sup_right : I₂ ≤ I₁ ⊔ I₂) x₂ →
      ∃ a : A, Ideal.Quotient.mk I₁ a = x₁ ∧ Ideal.Quotient.mk I₂ a = x₂ :=
  Ideal.injective_quotient_mk_prod_and_exists_of_factor_eq_of_inf_eq_bot
    I₁ I₂ h

/-- Higher-universe consumer: the theorem is not restricted to universe
0. -/
public example (A : Type 1) [CommRing A] (I₁ I₂ : Ideal A)
    (h : I₁ ⊓ I₂ = ⊥) :
    Function.Injective
        (fun a : A => (Ideal.Quotient.mk I₁ a, Ideal.Quotient.mk I₂ a)) :=
  (Ideal.injective_quotient_mk_prod_and_exists_of_factor_eq_of_inf_eq_bot
    I₁ I₂ h).1

/-- Without `I₁ ⊓ I₂ = ⊥` injectivity fails: for `I₁ = I₂ = ⊥` in `ℤ`
the map is injective, but for `I₁ = I₂ = ⊤`-like overlap the kernel is
the intersection. Here `I₁ = I₂ = (2)` in `ℤ`: `0` and `2` have the same
image, witnessing that the hypothesis is load-bearing. -/
public example : ¬ Function.Injective
    (fun a : ℤ => (Ideal.Quotient.mk (Ideal.span {2} : Ideal ℤ) a,
      Ideal.Quotient.mk (Ideal.span {2} : Ideal ℤ) a)) := by
  intro hinj
  have h02 : (0 : ℤ) = 2 := hinj (by
    simp only [Prod.mk.injEq, Ideal.Quotient.eq]
    constructor <;> simp [Ideal.mem_span_singleton])
  omega

end IdealMilnorSquareTest
