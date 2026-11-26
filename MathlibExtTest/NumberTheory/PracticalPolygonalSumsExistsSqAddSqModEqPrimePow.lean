/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PracticalPolygonalSumsExistsSqAddSqModEqPrimePow

/-!
# Tests for sums of two squares modulo prime powers

Concrete instances of the prime-power sum-of-two-squares theorem.
-/

namespace MathlibExtTest.NumberTheory.PracticalPolygonalSumsExistsSqAddSqModEqPrimePow

example : ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ^ 2 + y ^ 2 ≡ 5 [MOD 25] ∧ ¬ 5 ∣ y := by
  simpa using MetaMathlibExt.exists_sq_add_sq_modEq_prime_pow 5 5 2
    (by decide) (by decide) (by decide) (by decide)

example : ∃ x y : ℕ, x ^ 2 + y ^ 2 ≡ 1 [MOD 125] ∧ ¬ 5 ∣ y := by
  obtain ⟨x, y, _, _, h, hy⟩ := MetaMathlibExt.exists_sq_add_sq_modEq_prime_pow 5 1 3
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨x, y, h, hy⟩

end MathlibExtTest.NumberTheory.PracticalPolygonalSumsExistsSqAddSqModEqPrimePow
