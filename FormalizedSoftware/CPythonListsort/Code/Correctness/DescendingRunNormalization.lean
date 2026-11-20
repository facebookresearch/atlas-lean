/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

/-!
# Pure normalization algebra for descending natural runs

During `count_run`, the most recent comparator-equivalence block is reversed
before scanning continues.  At the end the whole descending prefix is
reversed.  These list identities isolate that double-reversal bookkeeping from
the executable array proof.
-/

namespace CPythonListsort

namespace DescendingRunSpec

/-- Reverse the final `tailLength` entries of a scanned descending prefix. -/
def reverseSuffix (xs : List α) (tailLength : Nat) : List α :=
  xs.take (xs.length - tailLength) ++
    (xs.drop (xs.length - tailLength)).reverse

/-- Stable ascending result represented by a descending prefix whose final
equivalence block has length `tailLength`. -/
def normalize (xs : List α) (tailLength : Nat) : List α :=
  xs.drop (xs.length - tailLength) ++
    (xs.take (xs.length - tailLength)).reverse

/-- Normalization is exactly whole-prefix reversal after reversing the final
equivalence block. -/
theorem normalize_eq_reverse_reverseSuffix (xs : List α)
    (tailLength : Nat) :
    normalize xs tailLength = (reverseSuffix xs tailLength).reverse := by
  simp [normalize, reverseSuffix, List.reverse_append]

/-- The first `tailLength` normalized entries are precisely the final
equivalence block, in their original order. -/
theorem normalize_take_eq_suffix (xs : List α) (tailLength : Nat)
    (htail : tailLength ≤ xs.length) :
    (normalize xs tailLength).take tailLength =
      xs.drop (xs.length - tailLength) := by
  have hlength :
      (xs.drop (xs.length - tailLength)).length = tailLength := by
    simp
    omega
  simp [normalize, hlength]

/-- Dropping the leading equivalence block leaves the reversal of the earlier
strictly descending prefix. -/
theorem normalize_drop_eq_reverse_prefix (xs : List α)
    (tailLength : Nat) (htail : tailLength ≤ xs.length) :
    (normalize xs tailLength).drop tailLength =
      (xs.take (xs.length - tailLength)).reverse := by
  have hlength :
      (xs.drop (xs.length - tailLength)).length = tailLength := by
    simp
    omega
  simp [normalize, hlength]

/-- Extending the final equivalence block inserts the new occurrence after
the existing block in normalized order. -/
theorem normalize_append_equivalent (xs : List α) (x : α)
    (tailLength : Nat) (htail : tailLength ≤ xs.length) :
    normalize (xs ++ [x]) (tailLength + 1) =
      (normalize xs tailLength).take tailLength ++ [x] ++
        (normalize xs tailLength).drop tailLength := by
  rw [normalize_take_eq_suffix xs tailLength htail,
    normalize_drop_eq_reverse_prefix xs tailLength htail]
  simp only [normalize, List.length_append, List.length_singleton]
  have hsub : xs.length + 1 - (tailLength + 1) =
      xs.length - tailLength := by
    omega
  rw [hsub]
  rw [List.drop_append_of_le_length
    (by omega : xs.length - tailLength ≤ xs.length)]
  rw [List.take_append_of_le_length
    (by omega : xs.length - tailLength ≤ xs.length)]

/-- After closing the prior equality block, a new strict-smaller entry becomes
the first entry of the normalized ascending result. -/
theorem normalize_after_strict (xs : List α) (x : α)
    (tailLength : Nat) :
    normalize (reverseSuffix xs tailLength ++ [x]) 1 =
      x :: normalize xs tailLength := by
  have hlength : (reverseSuffix xs tailLength).length = xs.length := by
    simp [reverseSuffix]
  simp only [normalize, List.length_append, List.length_singleton, hlength]
  have hsub : xs.length + 1 - 1 = xs.length := by
    omega
  rw [hsub]
  rw [List.drop_append_of_le_length (by simp [hlength])]
  rw [List.take_append_of_le_length (by simp [hlength])]
  have hdrop : (reverseSuffix xs tailLength).drop xs.length = [] := by
    rw [← hlength]
    simp
  have htake :
      (reverseSuffix xs tailLength).take xs.length =
        reverseSuffix xs tailLength := by
    rw [← hlength]
    simp
  rw [hdrop, htake]
  simp [reverseSuffix, List.reverse_append]

end DescendingRunSpec

end CPythonListsort
