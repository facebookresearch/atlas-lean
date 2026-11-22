/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Kolmogorov.Incompressible

@[expose] public section

/-!
# Tests for incompressible strings and the uncomputability of Kolmogorov complexity
-/

set_option autoImplicit false

open Cslib.Kolmogorov

namespace CSLibExtTest.Computability.Kolmogorov.Incompressible

/-- An incompressible string of length `5`. -/
example : ∃ x : List Bool, x.length = 5 ∧ 5 ≤ K x := exists_incompressible 5

/-- Complexity is unbounded. -/
example (n : ℕ) : ∃ x, n ≤ K x := (exists_incompressible n).imp fun _ h ↦ h.2

/-- Padding keeps the length. -/
example : (pad 4 [true]).length = 4 := rfl

/-- Fewer than `2 ^ 3` strings of length `10` are compressible below `3`, i.e. by `7`. -/
example : ((stringsOfLength 10).filter fun x ↦ K x < 10 - 7).card < 2 ^ (10 - 7) :=
  card_compressible_lt 10 7

/-- At most one string has complexity `0`: the empty description describes at most one string. -/
example (S : Finset (List Bool)) (hS : ∀ x ∈ S, K x < 1) : S.card ≤ 1 := by
  have := card_lt_two_pow S hS
  omega

example : ¬Computable K := not_computable_K

end CSLibExtTest.Computability.Kolmogorov.Incompressible
