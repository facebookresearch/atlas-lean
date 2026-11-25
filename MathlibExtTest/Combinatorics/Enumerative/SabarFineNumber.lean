/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SabarFineNumber

/-! # Boundary and sign checks for the alternating formula for Fine numbers -/

open MetaMathlibExt

-- The first admissible index has positive correction, and the next has negative correction.
example : fineNumber 2 = 1 := by
  rw [fineNumber_eq_half_neg_one_pow_add_sum 2 (by decide)]
  decide +kernel

example : fineNumber 3 = 2 := by
  rw [fineNumber_eq_half_neg_one_pow_add_sum 3 (by decide)]
  decide +kernel
