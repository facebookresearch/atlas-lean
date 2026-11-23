/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfect

namespace MathlibExt.NumberTheory.FkPerfectWanted

-- Both parity cases occur: 18 has the odd omitted divisor 3, and 54 has the even one 6.
example : KLNearPerfectWith 3 53 18 3 := by
  unfold KLNearPerfectWith
  decide

example : KLNearPerfectWith 9 144895263260 54 6 := by
  unfold KLNearPerfectWith
  decide

-- For 18, every omitted divisor is odd, including when the exponent and multiplier vary.
example {k l d : ℕ} (hk : 1 < k) (hl : 1 ≤ l) (h : KLNearPerfectWith k l 18 d) :
    9 ∣ 1 + 2 ^ k ∧ Odd d := by
  obtain ⟨hsq, hpar⟩ := klNearPerfectWith_two_mul_prime_pow_imp 3 2 k l d
    Nat.prime_three (by decide) hk hl h
  exact ⟨hsq, hpar.mp (by decide)⟩

end MathlibExt.NumberTheory.FkPerfectWanted
