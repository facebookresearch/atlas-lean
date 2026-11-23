/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedFrobeniusTriangular

/-! # Tests for splitting representations of a reduced triangular triple -/

open MetaMathlibExt

-- At n = 2 the triple (3, 6, 10) reduces to (3, 3, 5).
-- Below the first generator, every representation has first coefficient zero.
example (m : ℕ) (hm : m < 3) :
    frobeniusRepCount ![3, 3, 5] m = frobeniusRepCount ![3, 5] m := by
  have h := frobeniusRepCount_triangular_reduced_eq_sum 2 (by decide) m
  change frobeniusRepCount ![3, 3, 5] m = ∑ j ∈ Finset.range (m / 3 + 1),
    frobeniusRepCount ![3, 5] ((m : ℤ) - j * 3) at h
  simpa [Nat.div_eq_of_lt hm] using h

-- At the first multiple of 3, the last summand counts a representation of zero.
example : frobeniusRepCount ![3, 3, 5] 3 =
    frobeniusRepCount ![3, 5] 3 + frobeniusRepCount ![3, 5] 0 := by
  have h := frobeniusRepCount_triangular_reduced_eq_sum 2 (by decide) 3
  change frobeniusRepCount ![3, 3, 5] 3 = ∑ j ∈ Finset.range 2,
    frobeniusRepCount ![3, 5] (3 - (j : ℤ) * 3) at h
  simpa [Finset.sum_range_succ] using h
