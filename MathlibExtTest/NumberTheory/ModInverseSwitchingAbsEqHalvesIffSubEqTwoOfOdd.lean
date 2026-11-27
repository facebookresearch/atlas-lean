/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModInverseSwitchingAbsEqHalvesIffSubEqTwoOfOdd
import Lean.Elab.Tactic.Omega

/-!
# Tests for extremal first inverses

Concrete first remainders give absolute inverses of two and one. A gap greater than two
excludes simultaneous extremality by `abs_eq_halves_iff_sub_eq_two_of_odd`.
-/

namespace MathlibExtTest.NumberTheory.ModInverseSwitchingAbsEqHalvesIffSubEqTwoOfOdd

open MathlibExt.NumberTheory.ModInverseSwitchingWanted

example (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (hr₀ : r 0 = 5) (hr₁ : r 1 = 3) : |s 1| = 2 ∧ |s 2| = 1 := by
  have h₀ : Odd (r 0) := hr₀ ▸ (by decide : Odd (5 : ℕ))
  have h₁ : Odd (r 1) := hr₁ ▸ (by decide : Odd (3 : ℕ))
  have h := (abs_eq_halves_iff_sub_eq_two_of_odd r s N hseq h₀ h₁).mpr (by omega)
  rw [hr₀, hr₁] at h
  constructor <;> omega

example (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (h₀ : Odd (r 0)) (h₁ : Odd (r 1)) (hgap : r 1 + 2 < r 0) :
    ¬ (2 * |s 1| = (r 0 : ℤ) - 1 ∧ 2 * |s 2| = (r 1 : ℤ) - 1) := by
  intro h
  have := (abs_eq_halves_iff_sub_eq_two_of_odd r s N hseq h₀ h₁).mp h
  omega

end MathlibExtTest.NumberTheory.ModInverseSwitchingAbsEqHalvesIffSubEqTwoOfOdd
