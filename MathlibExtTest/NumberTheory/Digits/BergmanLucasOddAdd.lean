/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.BergmanLucasOddAdd
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Tests for the odd Lucas interval formulas for Bergman expansions
-/

open scoped goldenRatio

namespace MetaMathlibExt

private theorem golden_zpow_examples :
    φ ^ (2 : ℤ) = φ + 1 ∧ φ ^ (3 : ℤ) = 2 * φ + 1 ∧ φ ^ (5 : ℤ) = 5 * φ + 3 ∧
    φ ^ (-1 : ℤ) = φ - 1 ∧ φ ^ (-2 : ℤ) = 2 - φ ∧ φ ^ (-3 : ℤ) = 2 * φ - 3 ∧
    φ ^ (-4 : ℤ) = 5 - 3 * φ ∧ φ ^ (-6 : ℤ) = 13 - 8 * φ := by
  have hp (i : ℤ) : φ ^ (i + 1) = φ ^ i * φ := zpow_add_one₀ Real.goldenRatio_ne_zero i
  have hn (i : ℤ) : φ ^ (i - 1) = φ ^ i * (φ - 1) := by
    rw [zpow_sub_one₀ Real.goldenRatio_ne_zero, Real.inv_goldenRatio, ← Real.one_sub_goldenConj]
    ring
  have h2 : φ ^ (2 : ℤ) = φ + 1 := by simp [Real.goldenRatio_sq]
  have h3 : φ ^ (3 : ℤ) = 2 * φ + 1 := by
    calc φ ^ (3 : ℤ) = φ ^ (2 : ℤ) * φ := hp 2
      _ = _ := by rw [h2]; linear_combination Real.goldenRatio_sq
  have h4 : φ ^ (4 : ℤ) = 3 * φ + 2 := by
    calc φ ^ (4 : ℤ) = φ ^ (3 : ℤ) * φ := hp 3
      _ = _ := by rw [h3]; linear_combination 2 * Real.goldenRatio_sq
  have h5 : φ ^ (5 : ℤ) = 5 * φ + 3 := by
    calc φ ^ (5 : ℤ) = φ ^ (4 : ℤ) * φ := hp 4
      _ = _ := by rw [h4]; linear_combination 3 * Real.goldenRatio_sq
  have h1n : φ ^ (-1 : ℤ) = φ - 1 := by simpa using hn 0
  have h2n : φ ^ (-2 : ℤ) = 2 - φ := by
    calc φ ^ (-2 : ℤ) = φ ^ (-1 : ℤ) * (φ - 1) := by
          simpa only [show (-1 : ℤ) - 1 = -2 by decide] using hn (-1)
      _ = _ := by rw [h1n]; linear_combination Real.goldenRatio_sq
  have h3n : φ ^ (-3 : ℤ) = 2 * φ - 3 := by
    calc φ ^ (-3 : ℤ) = φ ^ (-2 : ℤ) * (φ - 1) := by
          simpa only [show (-2 : ℤ) - 1 = -3 by decide] using hn (-2)
      _ = _ := by rw [h2n]; linear_combination -Real.goldenRatio_sq
  have h4n : φ ^ (-4 : ℤ) = 5 - 3 * φ := by
    calc φ ^ (-4 : ℤ) = φ ^ (-3 : ℤ) * (φ - 1) := by
          simpa only [show (-3 : ℤ) - 1 = -4 by decide] using hn (-3)
      _ = _ := by rw [h3n]; linear_combination 2 * Real.goldenRatio_sq
  have h5n : φ ^ (-5 : ℤ) = 5 * φ - 8 := by
    calc φ ^ (-5 : ℤ) = φ ^ (-4 : ℤ) * (φ - 1) := by
          simpa only [show (-4 : ℤ) - 1 = -5 by decide] using hn (-4)
      _ = _ := by rw [h4n]; linear_combination -3 * Real.goldenRatio_sq
  have h6n : φ ^ (-6 : ℤ) = 13 - 8 * φ := by
    calc φ ^ (-6 : ℤ) = φ ^ (-5 : ℤ) * (φ - 1) := by
          simpa only [show (-5 : ℤ) - 1 = -6 by decide] using hn (-5)
      _ = _ := by rw [h5n]; linear_combination 5 * Real.goldenRatio_sq
  exact ⟨h2, h3, h5, h1n, h2n, h3n, h4n, h6n⟩

-- Two adjacent occupied positions do not form a Bergman expansion.
example : ¬ IsBergmanExpansion ({0, 1} : Finset ℤ) := by
  rw [isBergmanExpansion_iff]
  decide

-- The first formula at n = 2 and k = 1 changes 5 to 12, retaining the digit at −1.
example : ∃ b : ℤ, ({5, -1, -3, -6} : Finset ℤ) =
    {b, b + 3, b + 7 + 4} ∪ ({-1} : Finset ℤ).image (· + (b - (-4) + 2)) := by
  obtain ⟨_, h3, h5, h1n, _, h3n, h4n, h6n⟩ := golden_zpow_examples
  have hS : basePhiValue {3, -1, -4} = 5 := by
    rw [basePhiValue_eq_sum, Finset.sum_insert (by decide), Finset.sum_pair (by decide), h3, h1n, h4n]
    ring
  have hT : basePhiValue {5, -1, -3, -6} = 12 := by
    rw [basePhiValue_eq_sum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_pair (by decide), h5, h1n, h3n, h6n]
    ring
  have h := (bergman_lucas_odd_add 2 (by decide)).1 1 (by decide) (by decide)
    {3, -1, -4} {5, -1, -3, -6} (-4) 3 (by rw [isBergmanExpansion_iff]; decide) hS
    (by norm_num [IsLeast, lowerBounds]) (by norm_num [IsGreatest, upperBounds])
    (by rw [isBergmanExpansion_iff]; decide) hT
  have hI : (({3, -1, -4} : Finset ℤ).erase (-4)).erase 3 = {-1} := by decide
  simpa only [hI, show (3 : ℤ) - (-4) = 7 by decide] using h

-- The second formula at the upper endpoint k = 2 changes 6 to 17 and keeps the top digit of 6.
example : ∃ b : ℤ, ({5, 3, 1, -6} : Finset ℤ) =
    {b, b + 7 + 2, b + 7 + 4} ∪ ({1} : Finset ℤ).image (· + (b - (-4) + 2)) := by
  obtain ⟨_, h3, h5, _, _, _, h4n, h6n⟩ := golden_zpow_examples
  have hS : basePhiValue {3, 1, -4} = 6 := by
    rw [basePhiValue_eq_sum, Finset.sum_insert (by decide), Finset.sum_pair (by decide), h3, zpow_one, h4n]
    ring
  have hT : basePhiValue {5, 3, 1, -6} = 17 := by
    rw [basePhiValue_eq_sum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_pair (by decide), h5, h3, zpow_one, h6n]
    ring
  have h := (bergman_lucas_odd_add 2 (by decide)).2.1 2 (by decide) (by decide)
    {3, 1, -4} {5, 3, 1, -6} (-4) 3 (by rw [isBergmanExpansion_iff]; decide) hS
    (by norm_num [IsLeast, lowerBounds]) (by norm_num [IsGreatest, upperBounds])
    (by rw [isBergmanExpansion_iff]; decide) hT
  have hI : (({3, 1, -4} : Finset ℤ).erase (-4)).erase 3 = {1} := by decide
  simpa only [hI, show (3 : ℤ) - (-4) = 7 by decide] using h

-- The third formula accepts k = 0, when the expansion of 3 has no interior digits.
example : ∃ b : ℤ, ({5, 2, -3, -6} : Finset ℤ) = {b, b + 3, b + 4 + 4, b + 4 + 7} := by
  obtain ⟨h2, _, h5, _, h2n, h3n, _, h6n⟩ := golden_zpow_examples
  have hS : basePhiValue {2, -2} = 3 := by
    rw [basePhiValue_eq_sum, Finset.sum_pair (by decide), h2, h2n]
    ring
  have hT : basePhiValue {5, 2, -3, -6} = 14 := by
    rw [basePhiValue_eq_sum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_pair (by decide), h5, h2, h3n, h6n]
    ring
  have h := (bergman_lucas_odd_add 2 (by decide)).2.2 0 (by decide)
    {2, -2} {5, 2, -3, -6} (-2) 2 (by rw [isBergmanExpansion_iff]; decide) hS
    (by norm_num [IsLeast, lowerBounds]) (by norm_num [IsGreatest, upperBounds])
    (by rw [isBergmanExpansion_iff]; decide) hT
  have hI : (({2, -2} : Finset ℤ).erase (-2)).erase 2 = ∅ := by decide
  simpa only [hI, Finset.image_empty, Finset.union_empty, show (2 : ℤ) - (-2) = 4 by decide] using h

-- At the upper endpoint k = 1, the third formula sends 4 to 15 and keeps position 0.
example : ∃ b : ℤ, b = -6 ∧ ({5, 2, 0, -3, -6} : Finset ℤ) =
    {b, b + 3, b + 8, b + 11} ∪ {b + 6} := by
  obtain ⟨h2, _, h5, _, h2n, h3n, _, h6n⟩ := golden_zpow_examples
  have hS : basePhiValue {2, 0, -2} = 4 := by
    rw [basePhiValue_eq_sum, Finset.sum_insert (by decide), Finset.sum_pair (by decide),
      h2, zpow_zero, h2n]
    ring
  have hT : basePhiValue {5, 2, 0, -3, -6} = 15 := by
    rw [basePhiValue_eq_sum, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_pair (by decide), h5, h2, zpow_zero, h3n, h6n]
    ring
  obtain ⟨b, hb⟩ := (bergman_lucas_odd_add 2 (by decide)).2.2 1 (by decide)
    {2, 0, -2} {5, 2, 0, -3, -6} (-2) 2 (by rw [isBergmanExpansion_iff]; decide) hS
    (by norm_num [IsLeast, lowerBounds]) (by norm_num [IsGreatest, upperBounds])
    (by rw [isBergmanExpansion_iff]; decide) hT
  have hI : (({2, 0, -2} : Finset ℤ).erase (-2)).erase 2 = {0} := by decide
  have hshape : ({5, 2, 0, -3, -6} : Finset ℤ) = {b, b + 3, b + 8, b + 11} ∪ {b + 6} := by
    simpa only [hI, Finset.image_singleton, zero_add, show b + (2 - (-2)) + 4 = b + 8 by omega,
      show b + (2 - (-2)) + 7 = b + 11 by omega, show b - (-2) + 4 = b + 6 by omega] using hb
  -- The least position of the concrete output must be the replacement's least position.
  have hlow : b ∈ ({5, 2, 0, -3, -6} : Finset ℤ) := by rw [hshape]; simp
  have hhigh : (-6 : ℤ) ∈ ({b, b + 3, b + 8, b + 11} ∪ {b + 6} : Finset ℤ) :=
    hshape ▸ (by decide : (-6 : ℤ) ∈ ({5, 2, 0, -3, -6} : Finset ℤ))
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hlow hhigh
  exact ⟨b, by omega, hshape⟩

end MetaMathlibExt
