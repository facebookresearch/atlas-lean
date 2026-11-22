/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.ProductRings
import Mathlib.Tactic.Ring

/-!
# Tests for the product-ring / nontrivial-idempotent equivalence

`ℤ × ℤ` is a product of two nontrivial rings, so it has a nontrivial
idempotent; `ZMod 6` has the nontrivial idempotent `3`, so it is a product of
two nontrivial rings; `ℤ` has no nontrivial idempotent, so it is not a
product of two nontrivial rings.
-/

@[expose] public section

namespace MathlibExtTest.RingTheory.ProductRings

open _root_.ProductRings

/-- `ℤ × ℤ` has a nontrivial idempotent (it is a product of two nontrivial
rings). -/
private theorem int_prod_has_nontrivial_idempotent :
    ∃ e : ℤ × ℤ, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 :=
  (ring_product_iff_nontrivial_idempotent (ℤ × ℤ)).mp
    ⟨ℤ, ℤ, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨RingEquiv.refl _⟩⟩

/-- `ZMod 6` is a product of two nontrivial rings, via its nontrivial
idempotent `3`. -/
private theorem zmod_six_is_product :
    ∃ (R S : Type) (_ : Ring R) (_ : Ring S) (_ : Nontrivial R) (_ : Nontrivial S),
      Nonempty (ZMod 6 ≃+* R × S) :=
  (ring_product_iff_nontrivial_idempotent (ZMod 6)).mpr
    ⟨3, by show (3 : ZMod 6) * 3 = 3; decide, by decide, by decide⟩

/-- The only idempotents of `ℤ` are `0` and `1`. -/
private theorem int_idempotent_eq_zero_or_one {e : ℤ} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have h : e * (e - 1) = 0 := by
    have h' : e * (e - 1) = e * e - e := by ring
    rw [h', he.eq, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- `ℤ` is not a product of two nontrivial rings. -/
private theorem int_not_product :
    ¬∃ (R S : Type) (_ : Ring R) (_ : Ring S) (_ : Nontrivial R) (_ : Nontrivial S),
      Nonempty (ℤ ≃+* R × S) := by
  intro h
  obtain ⟨e, he, he0, he1⟩ := (ring_product_iff_nontrivial_idempotent ℤ).mp h
  rcases int_idempotent_eq_zero_or_one he with h | h
  · exact he0 h
  · exact he1 h

end MathlibExtTest.RingTheory.ProductRings
