/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SolubleTypeRecognitionKourovka12Problem37
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Defs

/-! # Tests for `MathlibExt.GroupTheory.SolubleTypeRecognitionKourovka12Problem37` -/

open MathlibExt.GroupTheory.SolubleTypeRecognitionKourovka12Problem37Wanted

-- The theorem refutes the statement of Kourovka Problem 12.37, here unfolded.
example : ¬ ∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H],
    Group.IsSolvable H → SameType G H → Group.IsSolvable G :=
  solubleOfSameTypeAsSoluble_refuted

-- Equivalently, some finite group of the same type as a finite soluble group is not soluble.
example : ∃ (G H : Type) (_ : Group G) (_ : Finite G) (_ : Group H) (_ : Finite H),
    Group.IsSolvable H ∧ SameType G H ∧ ¬ Group.IsSolvable G := by
  by_contra h
  refine solubleOfSameTypeAsSoluble_refuted fun G H _ _ _ _ hH hGH => ?_
  by_contra hG
  exact h ⟨G, H, inferInstance, inferInstance, inferInstance, inferInstance, hH, hGH, hG⟩

-- Having the same type is reflexive and symmetric.
example (G : Type) [Group G] : SameType G G := fun _ _ => rfl

example (G H : Type) [Group G] [Group H] (h : SameType G H) : SameType H G :=
  fun n hn => (h n hn).symm

-- Isomorphic groups have the same type.
example (G H : Type) [Group G] [Group H] (e : G ≃* H) : SameType G H := fun n _ =>
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    change x ^ n = 1 ↔ e x ^ n = 1
    rw [← map_pow]
    exact e.map_eq_one_iff.symm)

-- The cyclic group of order `4` and the Klein four-group have different types: `x ^ 2 = 1` has
-- two solutions in the first and four in the second.
example : ¬ SameType (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2 × ZMod 2)) := by
  intro h
  have h2 := h 2 (by decide)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype] at h2
  revert h2
  decide
