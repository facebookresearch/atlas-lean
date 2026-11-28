/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NarayanaSierpinski
import Mathlib.Order.Interval.Finset.Nat

namespace MetaMathlibExt

-- Even after discarding every value up to a bound, there is a witness at the least exponent.
example (b : ℕ) : ∃ t, b < narayanaCowsSequence t ∧ Odd (narayanaCowsSequence t) ∧
    ¬ (narayanaCowsSequence t * 2 + 1).Prime := by
  obtain ⟨k, ⟨hk, t, rfl⟩, ht⟩ := infinite_setOf_isSierpinskiNumber_narayanaCowsSequence.exists_gt b
  exact ⟨t, ht, hk.1, by simpa only [pow_one] using hk.2 1 le_rfl⟩

-- At the first listed index, the term is odd and the least positive exponent gives a nonprime.
example : Odd (narayanaCowsSequence 3629412) ∧
    ¬ (narayanaCowsSequence 3629412 * 2 - 1).Prime := by
  have h := isRieselNumber_narayanaCowsSequence (t := 3629412) (by decide)
  exact ⟨h.1, by simpa only [pow_one] using h.2 1 le_rfl⟩

-- The last listed index still works after shifting by any number of full periods.
example (q : ℕ) : IsRieselNumber (narayanaCowsSequence (703725732 + 718391520 * q)) := by
  apply isRieselNumber_narayanaCowsSequence
  rw [Nat.add_mul_mod_self_left]
  decide

end MetaMathlibExt
