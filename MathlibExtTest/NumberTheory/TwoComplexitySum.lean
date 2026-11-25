/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoComplexitySum

/-! # Tests for the 2-complexity bound on sums of powers of two -/

namespace MathlibExt.NumberTheory.TwoComplexityWanted

-- A singleton incurs no extra cost for addition.
example (m : ℕ) (hm : 1 ≤ m) : complexityL 2 (2 ^ m) ≤ m := by
  simpa using complexityL_sum_two_pow_le {m} (by simpa using hm) (Finset.singleton_nonempty m)

-- The exponents 2, 5 and 9 have gaps and a common power of two to factor out.
example : complexityL 2 548 ≤ 11 :=
  complexityL_sum_two_pow_le {2, 5, 9} (by decide) (by decide)

end MathlibExt.NumberTheory.TwoComplexityWanted
