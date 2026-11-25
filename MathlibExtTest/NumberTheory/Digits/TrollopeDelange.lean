/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.TrollopeDelange
import Mathlib.Tactic.NormNum

/-! # Tests for the Trollope–Delange bounds -/

open Asymptotics Filter MetaMathlibExt

-- At the smallest admissible base, the asymptotic bound gives a single bound on a real tail.
example : ∃ C X : ℝ, ∀ x ≥ X, |trollopeDelangeIntegral 2 x| ≤ C := by
  obtain ⟨C, hC⟩ := (isBigO_one_iff ℝ).mp (trollopeDelangeIntegral_isBigO_one 2 le_rfl)
  exact ⟨C, eventually_atTop.mp (eventually_map.mp hC)⟩

namespace MetaMathlibExt.digitSum_reciprocal_fluctuation_sum_le

open Real

-- On the first binary half-interval the centered digit is constantly -1/2 in the interior.
example : trollopeDelangeIntegral 2 (1 / 2) = -(1 / 4) := by
  calc
    _ = ∫ _ : ℝ in 0..1 / 2, -(1 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      have h₁ : ⌊t⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨ht.1.le, by linarith [ht.2]⟩
      have h₂ : ⌊2 * t⌋ = 0 :=
        Int.floor_eq_zero_iff.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      norm_num [h₁, h₂]
    _ = _ := by norm_num

-- Below the first positive integer the weighted sum is empty, including for negative cutoffs.
example (q : ℕ) (x y : ℝ) (hy : y < 1) :
    (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ((Nat.digits q n).sum : ℝ) / n *
      trollopeDelangeFluctuation q (log (x / n) / log q)) = 0 := by
  simp [Nat.floor_eq_zero.mpr hy]

-- At cutoff 5/2 the two binary digit sums are both one, giving weights 1 and 1/2.
example (x : ℝ) (hx : 0 < x) :
    trollopeDelangeFluctuation 2 (log x / log 2) +
      1 / 2 * trollopeDelangeFluctuation 2 (log (x / 2) / log 2) ≤
      (⨆ t : ℝ, |trollopeDelangeFluctuation 2 t|) * (3 / 2) := by
  have h := digitSum_reciprocal_fluctuation_sum_le 2 (by decide) x (5 / 2) hx
  have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have h₁ : (Nat.digits 2 1).sum = 1 := by decide
  have h₂ : (Nat.digits 2 2).sum = 1 := by decide
  have hfloor : ⌊(5 / 2 : ℝ)⌋₊ = 2 := (Nat.floor_eq_iff (by norm_num)).2 (by norm_num)
  rw [hfloor, hI] at h
  norm_num [h₁, h₂, Finset.sum_insert] at h
  exact h

end MetaMathlibExt.digitSum_reciprocal_fluctuation_sum_le
