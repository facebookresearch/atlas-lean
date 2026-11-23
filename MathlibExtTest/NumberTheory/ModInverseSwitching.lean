/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModInverseSwitching

open MathlibExt.NumberTheory.ModInverseSwitchingWanted

-- A negative representative of 3 modulo 5 gives a switching pair.
example : ∃ x y : ℤ, x * (-2) ≡ 1 [ZMOD 5] ∧ y * 5 ≡ 1 [ZMOD 3] ∧ x * 3 + y * 5 = 1 :=
  (exists_eq_mul_add_iff_switching 3 5 (by decide) (by decide) (-2) (by decide) (by decide)).mp
    ⟨1, by decide⟩

-- The switching pair (-2, 1) for 2 and 5 recovers a negative quotient when t = 7.
example : ∃ k : ℤ, 2 = k * 5 + 7 :=
  (exists_eq_mul_add_iff_switching 2 5 (by decide) (by decide) 7 (by decide) (by decide)).mpr
    ⟨-2, 1, by decide, by decide, by decide⟩

-- With n = 1 the representative t = 0 is allowed.
example : ∃ x y : ℤ, x * 0 ≡ 1 [ZMOD 1] ∧ y * 1 ≡ 1 [ZMOD 3] ∧ x * 3 + y * 1 = 1 :=
  (exists_eq_mul_add_iff_switching 3 1 (by decide) (by decide) 0 (by decide) (by decide)).mp
    ⟨3, by decide⟩

-- For modulus two, only the positive endpoint is a least absolute inverse.
example : IsLeastAbsInverse 1 1 2 ∧ ¬ IsLeastAbsInverse (-1) 1 2 := by
  unfold IsLeastAbsInverse
  decide

-- A switching sequence requires at least one Euclidean division.
example (r : ℕ → ℕ) (s : ℕ → ℤ) : ¬ IsEuclidSwitchSeq r s 0 :=
  fun h => (Nat.lt_irrefl 0) h.1
