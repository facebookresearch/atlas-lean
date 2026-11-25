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
