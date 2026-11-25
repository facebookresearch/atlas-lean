/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.ModularGroupFreeProduct
public import MathlibExt.NumberTheory.ModularForms.ModularGroupSerreTree

@[expose] public section

open scoped MatrixGroups

/-- Source consumer with the original binders. -/
private theorem exactSource :
    ∃ e : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2)))
        ≃* Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
            ℤ),
      e (Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 0)
          (Multiplicative.ofAdd 1)) = QuotientGroup.mk ModularGroup.S ∧
      e (Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 1)
          (Multiplicative.ofAdd 1)) = QuotientGroup.mk (ModularGroup.S * ModularGroup.T) :=
  ModularGroup.exists_mulEquiv_freeProduct_quotient_center

/-- Source consumer with the original binders. -/
private theorem exactSource_sub {A : Type*} [AddCommGroup A]
    (c : SL(2, ℤ) → A) (hc : ∀ g, c (-g) = c g) :
    ∃ a b : SL(2, ℤ) → A, (∀ g, a (ModularGroup.S * g) = a g) ∧
      (∀ g, b (ModularGroup.S * ModularGroup.T * g) = b g) ∧ ∀ g, c g = b g - a g :=
  ModularGroup.exists_apply_eq_sub_of_apply_neg_eq c hc

universe u in
/-- A consumer at an arbitrary universe. -/
example {A : Type (u + 1)} [AddCommGroup A] (c : SL(2, ℤ) → A) (hc : ∀ g, c (-g) = c g) :
    ∃ a b : SL(2, ℤ) → A, (∀ g, a (ModularGroup.S * g) = a g) ∧
      (∀ g, b (ModularGroup.S * ModularGroup.T * g) = b g) ∧ ∀ g, c g = b g - a g :=
  exactSource_sub c hc
