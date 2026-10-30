/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one.lean` and
`P2M/Sol/S_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Fixed
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Galois extensions of prime degree

An extension of prime degree carrying a nontrivial automorphism is Galois,
the automorphism has order equal to the degree, and it generates the full
automorphism group.
-/

@[expose] public section

/-- In an extension of prime degree, a nontrivial automorphism witnesses
that the extension is Galois, has order equal to the degree, and generates
the automorphism group. -/
theorem AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    IsGalois K L ∧ orderOf σ = Module.finrank K L ∧ Subgroup.zpowers σ = ⊤ := by
  have : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  set H : Subgroup (L ≃ₐ[K] L) := Subgroup.zpowers σ with hH
  have h1 : Module.finrank (IntermediateField.fixedField H) L = orderOf σ := by
    rw [IntermediateField.finrank_fixedField_eq_card, hH, Nat.card_zpowers]
  have htower : Module.finrank K (IntermediateField.fixedField H) *
      Module.finrank (IntermediateField.fixedField H) L = Module.finrank K L :=
    Module.finrank_mul_finrank K (IntermediateField.fixedField H) L
  have hordpos : 0 < orderOf σ := orderOf_pos σ
  have hord_ne_one : orderOf σ ≠ 1 := fun h => hσ (orderOf_eq_one_iff.1 h)
  have hdvd : orderOf σ ∣ Module.finrank K L :=
    ⟨Module.finrank K (IntermediateField.fixedField H), by rw [← h1, mul_comm]; exact htower.symm⟩
  have hord : orderOf σ = Module.finrank K L := by
    rcases (Nat.dvd_prime hdeg).1 hdvd with h | h
    · exact absurd h hord_ne_one
    · exact h
  have hbot : IntermediateField.fixedField H = ⊥ := by
    rw [← IntermediateField.finrank_eq_one_iff]
    have h2 : Module.finrank K (IntermediateField.fixedField H) * Module.finrank K L =
        1 * Module.finrank K L := by
      rw [one_mul]
      conv_rhs => rw [← htower]
      rw [h1, hord]
    exact Nat.eq_of_mul_eq_mul_right hdeg.pos h2
  have hgal : IsGalois K L := by
    apply IsGalois.of_fixedField_eq_bot
    exact le_bot_iff.1 (hbot ▸ IntermediateField.fixedField_le le_top)
  refine ⟨hgal, hord, ?_⟩
  have := hgal
  apply Subgroup.eq_top_of_card_eq
  rw [hH, Nat.card_zpowers, hord, IsGalois.card_aut_eq_finrank]
