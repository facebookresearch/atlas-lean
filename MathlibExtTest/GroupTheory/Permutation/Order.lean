/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from `fairinternal/formal-math/MathlibExtTest/GroupTheory/Permutation/Order.lean`
at commit `5edfb3b6f668f04b907ff6ca3a98cb0ce1c2eb64`.
Original source SHA-256: f4000deef9797f0f0218a89d0247b17c27b7af01d478e42c424f9d45e717328d
-/

module

public import MathlibExt.GroupTheory.Permutation.Order

@[expose] public section

variable (α : Type*) [LT α]

/-- Carrier characterization: membership unfolds to the two-sided order condition. -/
example (σ : Equiv.Perm α) :
    σ ∈ MetaMathlibExt.orderAutSubgroup α ↔ ∀ a b, a < b ↔ σ a < σ b :=
  MetaMathlibExt.mem_orderAutSubgroup σ

/-- The identity permutation preserves `<`. -/
example : (1 : Equiv.Perm α) ∈ MetaMathlibExt.orderAutSubgroup α :=
  Subgroup.one_mem _

/-- Order automorphisms are closed under multiplication. -/
example {σ τ : Equiv.Perm α} (hσ : σ ∈ MetaMathlibExt.orderAutSubgroup α)
    (hτ : τ ∈ MetaMathlibExt.orderAutSubgroup α) :
    σ * τ ∈ MetaMathlibExt.orderAutSubgroup α :=
  Subgroup.mul_mem _ hσ hτ

/-- Order automorphisms are closed under inverse. -/
example {σ : Equiv.Perm α} (h : σ ∈ MetaMathlibExt.orderAutSubgroup α) :
    σ⁻¹ ∈ MetaMathlibExt.orderAutSubgroup α :=
  Subgroup.inv_mem _ h
