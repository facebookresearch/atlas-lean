/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.HypersequenceB

/-! # Tests for Parisse's matrix -/

open MetaMathlibExt

-- Compute the signs across the third row and the first entry beyond the diagonal.
example : (List.range 5).map (hyperseqB 0 3) = [6, -11, 6, -1, 0] := by
  decide +kernel

-- The Stirling formula gives the alternating diagonal, including the empty row product.
example (j : ℕ) : hyperseqB 0 j j = (-1) ^ j := by
  rw [(hyperseqB_zero_recurrence_stirling.2.2.2 j j).2]
  simp [Nat.stirlingFirst_self]

-- Above the diagonal the binomial sum is empty, regardless of the sign.
example {j k : ℕ} (h : j < k) : hyperseqB 0 j k = 0 := by
  rw [(hyperseqB_zero_recurrence_stirling.2.2.2 j k).1]
  simp [Finset.Icc_eq_empty_of_lt h]
