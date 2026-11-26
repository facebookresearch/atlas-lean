/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SZumkellerIsSquareOfIsSZumkellerOdd

/-!
# Tests for odd s-Zumkeller squares

An odd s-Zumkeller number has an odd square root.

Reference: Jayanta Kalita and Helen K. Saikia, *A Study on Generalized Zumkeller
Numbers*, INTEGERS 24 (2024), Article A95, Proposition 7.
-/

namespace MathlibExtTest.NumberTheory.SZumkellerIsSquareOfIsSZumkellerOdd

example (n : ℕ) (h : MetaMathlibExt.IsSZumkeller n) (ho : Odd n) :
    ∃ k : ℕ, Odd k ∧ n = k ^ 2 := by
  obtain ⟨k, hk⟩ := (MetaMathlibExt.isSquare_of_isSZumkeller_odd n h ho).exists_sq
  refine ⟨k, ?_, hk⟩
  exact (Nat.odd_pow_iff (by decide : 2 ≠ 0)).mp (hk ▸ ho)

end MathlibExtTest.NumberTheory.SZumkellerIsSquareOfIsSZumkellerOdd
