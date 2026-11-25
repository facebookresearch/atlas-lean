/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Basic.Countable.Basic

/-!
# Countability of the entire original finite-path family

Countable original vertices and original arrow sets give countably many
paths at every original ordered pair. The proof counts actual paths of
each length through their original final arrow and intermediate vertex,
then takes their countable union. Parallel arrows are retained.
-/

universe u v

namespace Quiver.Path

variable {V : Type u} [Quiver.{v} V] [Countable V]
variable [∀ x y : V, Countable (x ⟶ y)]

/-- Actual original paths with their complete prescribed length. -/
abbrev LengthFiber (n : ℕ) (a b : V) := {p : Path a b // p.length = n}

/-- Every finite length retains a countable set of SAME original paths, with all arrows and
intermediate vertices. -/
theorem countable_lengthFiber (n : ℕ) (a b : V) : Countable (LengthFiber n a b) := by
  induction n generalizing a b with
  | zero =>
    have : Subsingleton (LengthFiber 0 a b) := by
      constructor
      rintro ⟨p, hp⟩ ⟨q, hq⟩
      apply Subtype.ext
      cases p with
      | nil => exact (eq_nil_of_length_zero q hq).symm
      | cons p e => exact (Nat.succ_ne_zero _ hp).elim
    infer_instance
  | succ n ih =>
    have (c : V) : Countable (LengthFiber n a c) := ih a c
    let supply : (Σ c : V, LengthFiber n a c × (c ⟶ b)) → LengthFiber (n + 1) a b :=
      fun p => ⟨p.2.1.val.cons p.2.2, congrArg (fun k => k + 1) p.2.1.property⟩
    have hs : Function.Surjective supply := by
      rintro ⟨p, hp⟩
      cases p with
      | nil => exact (Nat.succ_ne_zero n hp.symm).elim
      | @cons c b p e =>
        have h : p.length = n := Nat.add_right_cancel hp
        exact ⟨⟨c, ⟨p, h⟩, e⟩, rfl⟩
    exact hs.countable

/-- The entire original path set is countable, retaining every length and parallel-arrow choice. -/
theorem countable_original_paths (a b : V) : Countable (Path a b) := by
  have (n : ℕ) : Countable (LengthFiber n a b) := countable_lengthFiber n a b
  let forget : (Σ n : ℕ, LengthFiber n a b) → Path a b := fun p => p.2.val
  exact (show Function.Surjective forget from fun p => ⟨⟨p.length, p, rfl⟩, rfl⟩).countable

end Quiver.Path
