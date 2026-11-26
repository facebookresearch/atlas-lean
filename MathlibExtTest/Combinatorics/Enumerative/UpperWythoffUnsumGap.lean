/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.UpperWythoffUnsumGap

namespace MetaMathlibExt

-- Gap indices start at zero, and the initial gap is a unit gap too.
example : upperWythoffUnsumGap 0 = 1 := by
  simpa using congrArg (fun gaps : List ℕ => gaps.getD 0 0) upperWythoffUnsumGap_small

-- The last unit gap is at index 9, with gaps of size two immediately on either side.
example : upperWythoffUnsumGap 8 = 2 ∧ upperWythoffUnsumGap 9 = 1 ∧
    upperWythoffUnsumGap 10 = 2 := by
  refine ⟨?_, upperWythoffUnsumGap_ne_one.1, ?_⟩
  · simpa using congrArg (fun gaps : List ℕ => gaps.getD 8 0) upperWythoffUnsumGap_small
  · simpa using congrArg (fun gaps : List ℕ => gaps.getD 10 0) upperWythoffUnsumGap_small

-- The exclusion starts at 10 itself and applies to every later index.
example : upperWythoffUnsumGap 10 ≠ 1 := upperWythoffUnsumGap_ne_one.2 10 le_rfl

example (j : ℕ) : upperWythoffUnsumGap (10 + j) ≠ 1 :=
  upperWythoffUnsumGap_ne_one.2 _ (Nat.le_add_right 10 j)

end MetaMathlibExt
