/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.NumberTheory.FkPerfect

/-! # Tests for prime powers that are `[k,ℓ]`-near-perfect -/

@[expose] public section

namespace MathlibExtTest.NumberTheory.FkPerfect

open MathlibExt.NumberTheory.FkPerfectWanted

-- The paper's example: σ₃(4) = 73 = 4³ + 1³ + 2 * 4.
example : KLNearPerfectWith 3 2 (2 ^ 2) 1 := by
  rw [klNearPerfectWith_prime_pow_iff 2 2 3 2 1 Nat.prime_two (by decide) (by decide)]
  exact ⟨by decide, by decide, rfl, by decide⟩

-- With a = 1 the required range 2 ≤ a fails.
example : ¬ KLNearPerfectWith 2 3 (2 ^ 1) 1 := by
  rw [klNearPerfectWith_prime_pow_iff 2 1 2 3 1 Nat.prime_two (by decide) (by decide)]
  decide

-- Corollary: the exponent is bounded by k.
theorem le_of_klNearPerfectWith_prime_pow (p a k l d : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hl : 1 ≤ l) (h : KLNearPerfectWith k l (p ^ a) d) : a ≤ k :=
  ((klNearPerfectWith_prime_pow_iff p a k l d hp hk hl).mp h).2.1

end MathlibExtTest.NumberTheory.FkPerfect
