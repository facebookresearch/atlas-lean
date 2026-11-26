/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.HypersequenceLucasClosedForm

open MetaMathlibExt

-- The empty correction sum leaves the original sequence at generation zero.
example (n : ℕ) : ((hypersequence lucasNumber 0 n : ℕ) : ℤ) = lucasNumber n := by
  simpa using hyperLucas_eq_lucas_sub_sum 0 n

-- At index zero, the correction sum leaves the initial Lucas value unchanged.
example : ((hypersequence lucasNumber 3 0 : ℕ) : ℤ) = 2 := by
  rw [hyperLucas_eq_lucas_sub_sum]
  decide

-- Check a case with several nontrivial correction terms against the iterated sums.
example : ((hypersequence lucasNumber 3 2 : ℕ) : ℤ) = 18 := by
  rw [hyperLucas_eq_lucas_sub_sum]
  decide

example : hypersequence lucasNumber 3 2 = 18 := by decide
