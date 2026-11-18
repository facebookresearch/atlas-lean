/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.Encoding

/-!
# Tests for the token encoding of LTL formulas

Concrete token lists, round trips, and rejection of ill-formed lists.
-/

@[expose] public section

namespace Cslib.LTL.EncodingTests

open Formula

example : tokens (.until (.atom 0) (.atom 1) : Formula ℕ) =
    [Nat.pair 5 0, Nat.pair 0 0, Nat.pair 0 1] := rfl

example : (tokens (Formula.always (Formula.eventually (.atom 3)) : Formula ℕ)).length = 7 := by
  rw [length_tokens]
  rfl

example : decodeList (tokens (Formula.release (.atom 0) (.next (.atom 2)) : Formula ℕ)) =
    some (Formula.release (.atom 0) (.next (.atom 2))) :=
  decodeList_tokens _

/-- The empty list and a conjunction with a missing argument decode to nothing. -/
example : decodeList [] = none := by decide

example : decodeList [Nat.pair 3 0, Nat.pair 0 0] = none := by
  simp [decodeList, parseFuel, Nat.unpair_pair]

/-- Trailing tokens are rejected. -/
example : decodeList [Nat.pair 1 0, Nat.pair 1 0] = none := by
  simp [decodeList, parseFuel, Nat.unpair_pair]

end Cslib.LTL.EncodingTests
