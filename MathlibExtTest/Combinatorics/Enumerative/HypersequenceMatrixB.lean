/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.HypersequenceMatrixB

/-! # Tests for Parisse's hypersequence matrix B -/

open MetaMathlibExt

-- The binomial sum in row three gives the interior coefficient of odd index.
example : hyperseqB 0 3 1 = -11 :=
  ((hyperseqB_zero_recurrence_stirling.2.2.2 3 1).1).trans (by decide)

-- On the diagonal there is one cycle partition into singleton cycles.
example (j : ℕ) : hyperseqB 0 j j = (-1) ^ j := by
  simpa [Nat.stirlingFirst_self] using (hyperseqB_zero_recurrence_stirling.2.2.2 j j).2

-- Above the diagonal the index interval for the binomial sum is empty.
example (j k : ℕ) (h : j < k) : hyperseqB 0 j k = 0 := by
  simpa [Finset.Icc_eq_empty_of_lt h] using (hyperseqB_zero_recurrence_stirling.2.2.2 j k).1

-- At a negative parameter the zero factor in row three kills the constant coefficient.
example : (List.range 4).map (hyperseqB (-1) 3) = [0, -2, 3, -1] := by
  decide +kernel

/-! ### Recurrence, closed form and row sums at nonnegative parameters -/

-- The empty row has one nonzero entry.
example (n : ℕ) : hyperseqB n 0 0 = 1 ∧ hyperseqB n 0 1 = 0 := by
  have h := (hyperseqB_recurrence_closed_form_row_sums n).1
  exact ⟨by simpa using h 0, by simpa using h 1⟩

-- At `n = 1` the recurrence multiplies by `4` when passing from row two to row three.
example : hyperseqB 1 3 0 = 24 ∧ hyperseqB 1 3 2 = 9 := by
  obtain ⟨_, hfirst, hstep, _⟩ := hyperseqB_recurrence_closed_form_row_sums 1
  exact ⟨(hfirst 2).trans (by decide +kernel), (hstep 2 1).trans (by decide +kernel)⟩

-- The closed form includes the signs, powers of `n + 1`, and the empty interval above the diagonal.
example : hyperseqB 1 3 1 = -26 :=
  ((hyperseqB_recurrence_closed_form_row_sums 1).2.2.2.1 3 1).trans (by decide +kernel)

example (n j k : ℕ) (h : j < k) : hyperseqB n j k = 0 := by
  simpa [Finset.Icc_eq_empty_of_lt h] using
    (hyperseqB_recurrence_closed_form_row_sums n).2.2.2.1 j k

-- The signs in an odd row distinguish the plain and alternating sums.
example : (∑ k ∈ Finset.range 4, hyperseqB 1 3 k) = 6 ∧
    (∑ k ∈ Finset.range 4, (-1) ^ k * hyperseqB 1 3 k) = 60 := by
  obtain ⟨_, _, _, _, hplain, halt⟩ := hyperseqB_recurrence_closed_form_row_sums 1
  exact ⟨(hplain 3).trans (by decide), (halt 3).trans (by decide)⟩
