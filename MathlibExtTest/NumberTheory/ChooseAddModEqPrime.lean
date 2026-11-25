/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ChooseAddModEqPrime

open MetaMathlibExt

-- At the last nonzero residue, the odd exponent gives the value -1.
example (n : ℕ) (hr : n % 7 = 3) : ((n + 3).choose 3 : ℤ) ≡ -1 [ZMOD 7] := by
  simpa [hr] using choose_add_modEq_prime 7 (by decide) ⟨3, rfl⟩ 3 (by decide) (by decide) n

-- The next residue makes the binomial coefficient divisible by 7.
example (n : ℕ) (hr : n % 7 = 4) : ((n + 3).choose 3 : ℤ) ≡ 0 [ZMOD 7] := by
  simpa [hr] using choose_add_modEq_prime 7 (by decide) ⟨3, rfl⟩ 3 (by decide) (by decide) n
