/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.PrimeCounting.ThinnedWallisPrimeProductAsymptotic

/-! # Tests for the thinned Wallis-type prime product asymptotic -/

open Filter Topology MetaMathlibExt

private noncomputable def wallisProduct (m : ℕ) (S : Finset (ZMod (2 ^ m))) (x : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
    ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4))

-- The negative character at 3 gives a growing factor of `log x`.
example : ∃ K : ℝ, 0 < K ∧
    Tendsto (fun x => wallisProduct 2 {3} x / (K * Real.log x)) atTop (𝓝 1) := by
  obtain ⟨K, hK, h⟩ := thinned_wallis_prime_product_asymptotic 2 le_rfl {3} (by decide)
  change Tendsto (fun x => wallisProduct 2 {3} x / (K * Real.log x ^
    (-2 * ((∑ a ∈ ({3} : Finset (ZMod 4)), ZMod.χ₄ (a.val : ZMod 4) : ℤ) : ℝ) /
      (Nat.totient 4 : ℝ)))) atTop (𝓝 1) at h
  exact ⟨K, hK, by simpa [show ZMod.χ₄ ((3 : ZMod 4).val : ZMod 4) = -1 by decide,
    show Nat.totient 4 = 2 by decide, show -2 * (-1 : ℝ) / 2 = 1 by norm_num] using h⟩

-- The positive character at 1 gives a decaying factor of `1 / log x`.
example : ∃ K : ℝ, 0 < K ∧
    Tendsto (fun x => wallisProduct 2 {1} x / (K / Real.log x)) atTop (𝓝 1) := by
  obtain ⟨K, hK, h⟩ := thinned_wallis_prime_product_asymptotic 2 le_rfl {1} (by decide)
  change Tendsto (fun x => wallisProduct 2 {1} x / (K * Real.log x ^
    (-2 * ((∑ a ∈ ({1} : Finset (ZMod 4)), ZMod.χ₄ (a.val : ZMod 4) : ℤ) : ℝ) /
      (Nat.totient 4 : ℝ)))) atTop (𝓝 1) at h
  refine ⟨K, hK, ?_⟩
  simpa [show ZMod.χ₄ ((1 : ZMod 4).val : ZMod 4) = 1 by decide,
    show Nat.totient 4 = 2 by decide, show -2 * (1 : ℝ) / 2 = -1 by norm_num,
    Real.rpow_neg_one, div_eq_mul_inv] using h

-- The classes 1 and 7 modulo 8 reduce to opposite characters modulo 4.
example : ∃ K : ℝ, 0 < K ∧ Tendsto (wallisProduct 3 {1, 7}) atTop (𝓝 K) := by
  obtain ⟨K, hK, h⟩ := thinned_wallis_prime_product_asymptotic 3 (by decide) {1, 7} (by decide)
  change Tendsto (fun x => wallisProduct 3 {1, 7} x / (K * Real.log x ^
    (-2 * ((∑ a ∈ ({1, 7} : Finset (ZMod 8)), ZMod.χ₄ (a.val : ZMod 4) : ℤ) : ℝ) /
      (Nat.totient 8 : ℝ)))) atTop (𝓝 1) at h
  rw [show (∑ a ∈ ({1, 7} : Finset (ZMod 8)), ZMod.χ₄ (a.val : ZMod 4)) = 0 by decide,
    Int.cast_zero, mul_zero, zero_div] at h
  simp only [Real.rpow_zero, mul_one] at h
  exact ⟨K, hK, by simpa only [div_mul_cancel₀ _ hK.ne', one_mul] using h.mul_const K⟩
