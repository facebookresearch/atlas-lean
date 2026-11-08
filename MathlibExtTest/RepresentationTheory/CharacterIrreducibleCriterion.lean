/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.CharacterIrreducibleCriterion
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

namespace MathlibExtTest.RepresentationTheory.CharacterIrreducibleCriterion

open CharacterTheory

universe u

/-- Every one-dimensional representation is irreducible: its subrepresentations
are the submodules of a one-dimensional space, hence only `⊥` and `⊤`. -/
theorem one_dim_rep_irreducible {G : Type u} [Group G] [Fintype G]
    {k : Type u} [Field k] (ρ : Representation k G k) :
    ρ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  refine (isSimpleModule_iff _ _).mpr ?_
  have h : Module.finrank k ρ.asModule = 1 := Module.finrank_self k
  exact is_simple_module_of_finrank_eq_one h

/-- The trivial representation of any finite group on `ℂ` is irreducible, so
its character has self-pairing `1` by the criterion (forward direction). -/
example {G : Type} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)] :
    classInnerProduct (Representation.trivial ℂ G ℂ).character
      (Representation.trivial ℂ G ℂ).character = 1 :=
  (irreducible_iff_classInnerProduct_self_eq_one
    (Representation.trivial ℂ G ℂ)).mp
    (one_dim_rep_irreducible (Representation.trivial ℂ G ℂ))

/-- The character of the trivial representation is constantly `1`, so its
self-pairing is `|G|⁻¹ * |G| = 1` by direct computation. The converse of the
criterion then proves that the representation is irreducible. -/
example {G : Type} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)] :
    (Representation.trivial ℂ G ℂ).IsIrreducible := by
  apply (irreducible_iff_classInnerProduct_self_eq_one
    (Representation.trivial ℂ G ℂ)).mpr
  have hne : (Nat.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos (α := G) |>.ne')
  have hchar : ∀ g : G, (Representation.trivial ℂ G ℂ).character g = 1 := by
    intro g
    have hρ : (Representation.trivial ℂ G ℂ) g = LinearMap.id := rfl
    rw [show (Representation.trivial ℂ G ℂ).character g =
        LinearMap.trace ℂ ℂ ((Representation.trivial ℂ G ℂ) g) from rfl,
      hρ, LinearMap.trace_id]
    simp
  rw [show classInnerProduct (Representation.trivial ℂ G ℂ).character
        (Representation.trivial ℂ G ℂ).character =
      (Nat.card G : ℂ)⁻¹ * (Fintype.card G : ℂ) from by
    simp only [classInnerProduct, hchar, mul_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one],
    ← Nat.card_eq_fintype_card, inv_mul_cancel₀ hne]

/-- The trivial representation on `ℂ × ℂ` has character constantly `2`, so
its self-pairing is `4 ≠ 1`; by contraposition of the forward direction it
is not irreducible. -/
example {G : Type} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)] :
    ¬ (Representation.trivial ℂ G (ℂ × ℂ)).IsIrreducible := by
  intro hirr
  have hpair := (irreducible_iff_classInnerProduct_self_eq_one
    (Representation.trivial ℂ G (ℂ × ℂ))).mp hirr
  have hchar : ∀ g : G, (Representation.trivial ℂ G (ℂ × ℂ)).character g = 2 := by
    intro g
    have hρ : (Representation.trivial ℂ G (ℂ × ℂ)) g = LinearMap.id := rfl
    rw [show (Representation.trivial ℂ G (ℂ × ℂ)).character g =
        LinearMap.trace ℂ (ℂ × ℂ) ((Representation.trivial ℂ G (ℂ × ℂ)) g) from rfl,
      hρ, LinearMap.trace_id]
    simp
  rw [classInnerProduct] at hpair
  simp only [hchar, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hpair
  have hcard : (Nat.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos (α := G) |>.ne')
  have h4 : (Nat.card G : ℂ)⁻¹ * ((Fintype.card G : ℂ) * (2 * 2)) = 4 := by
    rw [← Nat.card_eq_fintype_card, ← mul_assoc, inv_mul_cancel₀ hcard]
    norm_num
  rw [h4] at hpair
  norm_num at hpair

end MathlibExtTest.RepresentationTheory.CharacterIrreducibleCriterion
