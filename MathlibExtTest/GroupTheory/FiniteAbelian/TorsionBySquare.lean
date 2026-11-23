/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.FiniteAbelian.TorsionBySquare

@[expose] public section

-- `exactSource` consumer with the original binders.
example {A : Type*} [AddCommGroup A] {n : ℕ} (hn : n ≠ 0)
    (hcard : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ 2) :
    Nonempty (ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) :=
  AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq hn hcard

-- The cardinality hypothesis matters: for the trivial group and `n = 2` it
-- fails at `d = 2`, and the stated equivalence is false.
example : ¬ Nonempty (ZMod 2 × ZMod 2 ≃+ Submodule.torsionBy ℤ (ZMod 1) (2 : ℤ)) := by
  rintro ⟨e⟩
  have h := Nat.card_congr e.toEquiv
  rw [Nat.card_prod, Nat.card_zmod] at h
  have hle : Nat.card (Submodule.torsionBy ℤ (ZMod 1) (2 : ℤ)) ≤ Nat.card (ZMod 1) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  rw [Nat.card_zmod] at hle
  omega
