/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Ideal_injective_quotient_mk_prod_and_exists_of_factor_eq_of_inf_eq_bot.lean`
and
`P2M/Sol/S_Ideal_injective_quotient_mk_prod_and_exists_of_factor_eq_of_inf_eq_bot.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

namespace Ideal

/-- The Milnor square of two ideals with zero intersection: `A` embeds
into `A ⧸ I₁ × A ⧸ I₂`, and its image is exactly the pairs that agree
in `A ⧸ (I₁ ⊔ I₂)`. -/
public theorem injective_quotient_mk_prod_and_exists_of_factor_eq_of_inf_eq_bot
    {A : Type*} [CommRing A] (I₁ I₂ : Ideal A) (h : I₁ ⊓ I₂ = ⊥) :
    Function.Injective
        (fun a : A => (Ideal.Quotient.mk I₁ a, Ideal.Quotient.mk I₂ a)) ∧
    ∀ (x₁ : A ⧸ I₁) (x₂ : A ⧸ I₂),
      Ideal.Quotient.factor (le_sup_left : I₁ ≤ I₁ ⊔ I₂) x₁ =
        Ideal.Quotient.factor (le_sup_right : I₂ ≤ I₁ ⊔ I₂) x₂ →
      ∃ a : A, Ideal.Quotient.mk I₁ a = x₁ ∧ Ideal.Quotient.mk I₂ a = x₂ := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    simp only [Prod.mk.injEq, Ideal.Quotient.eq] at hab
    have : a - b ∈ I₁ ⊓ I₂ := ⟨hab.1, hab.2⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  · intro x₁ x₂ hx
    obtain ⟨a₁, rfl⟩ := Ideal.Quotient.mk_surjective x₁
    obtain ⟨a₂, rfl⟩ := Ideal.Quotient.mk_surjective x₂
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq, Submodule.mem_sup] at hx
    obtain ⟨i₁, hi₁, i₂, hi₂, hsum⟩ := hx
    refine ⟨a₁ - i₁, ?_, ?_⟩
    · rw [Ideal.Quotient.eq, sub_sub_cancel_left]; exact I₁.neg_mem hi₁
    · rw [Ideal.Quotient.eq,
        show a₁ - i₁ - a₂ = i₂ by rw [sub_right_comm, ← hsum]; ring]
      exact hi₂

end Ideal
