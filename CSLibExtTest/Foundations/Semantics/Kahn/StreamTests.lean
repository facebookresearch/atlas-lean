/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Foundations.Semantics.Kahn.Stream

/-! # Regression examples for Kahn stream prefixes -/

set_option autoImplicit false

namespace Cslib.Foundations.Semantics.Kahn.Stream.Tests

-- A finite stream is below an infinite one precisely on agreeing defined positions.
example : ofList [0, 1] ≤ ofStream (fun n : ℕ => n) := by
  rw [le_iff_get?]
  intro i a hi
  cases i with
  | zero =>
      change some (0 : ℕ) = some a
      exact hi
  | succ i =>
      cases i with
      | zero =>
          change some (1 : ℕ) = some a
          exact hi
      | succ i => simp at hi

-- Matching the first entry does not excuse a mismatch in a later defined entry.
example : ¬ ofList [0, 2] ≤ ofStream (fun n : ℕ => n) := by
  intro h
  have hbad := le_iff_get?.mp h 1 2 rfl
  cases hbad

-- A match at a later position does not make a non-prefix into a prefix.
example : ¬ ofList [1] ≤ ofStream (fun n : ℕ => n) := by
  intro h
  have hbad := le_iff_get?.mp h 0 1 rfl
  cases hbad

-- Termination at index 1 prevents a shorter stream from extending a two-entry stream.
example : ¬ ofList [0, 1] ≤ ofList [0] := by
  intro h
  have hbad := le_iff_get?.mp h 1 1 rfl
  cases hbad

example : ofList [0, 1] ≤ ofList [0, 1, 2] := by
  rw [ofList_le_ofList_iff]
  exact ⟨[2], rfl⟩

example : (⊥ : Stream Empty) = ofList [] := ofList_nil.symm

example {s : Stream ℕ} (h : ofStream (fun n : ℕ => n) ≤ s) :
    s = ofStream (fun n : ℕ => n) := (eq_of_ofStream_le h).symm

end Cslib.Foundations.Semantics.Kahn.Stream.Tests
