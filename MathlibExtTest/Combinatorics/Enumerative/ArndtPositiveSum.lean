/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ArndtPositiveSum

open MetaMathlibExt

-- One part: the only nonzero term is `C(-1, 0) C(n - 1, 0) = 1`.
example : (arndtCompositionCount (fun _ => True) 7 1 : ℤ) = 1 := by
  rw [arndtCompositionCount_eq_positive_sum 7 1 (by norm_num)]
  decide

-- Below the threshold `m + ⌊m/2⌋ ≤ n` there is no Arndt composition.
example : arndtCompositionCount (fun _ => True) 5 4 = 0 := by
  have h := arndtCompositionCount_eq_positive_sum 5 4 (by norm_num)
  norm_num at h
  exact h

-- Three terms: `a(10, 4) = C(1, 0) C(5, 1) + C(2, 1) C(3, 1) + C(3, 2) C(1, 1) = 14`.
example : (arndtCompositionCount (fun _ => True) 10 4 : ℤ) = 14 := by
  rw [arndtCompositionCount_eq_positive_sum 10 4 (by norm_num)]
  decide

-- Odd number of parts, two terms: `a(9, 5) = C(1, 0) C(4, 2) + C(2, 1) C(2, 2) = 8`.
example : (arndtCompositionCount (fun _ => True) 9 5 : ℤ) = 8 := by
  rw [arndtCompositionCount_eq_positive_sum 9 5 (by norm_num)]
  decide

-- The formula reproduces the four Arndt compositions of 6 with three parts.
example : (arndtCompositionCount (fun _ => True) 6 3 : ℤ) = 4 := by
  rw [arndtCompositionCount_eq_positive_sum 6 3 (by norm_num)]
  decide
