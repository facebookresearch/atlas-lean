/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Padics.MoritaGammaPadic

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Tests for Morita's `p`-adic gamma function on `ℤ_[p]`
-/

@[expose] public section

open MetaMathlibExt

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ### Small values: `Γ_p(n) = (-1) ^ n ∏_{j < n, p ∤ j} j` -/

example (p : ℕ) [Fact p.Prime] : moritaGamma p 0 = 1 := by simp
example (p : ℕ) [Fact p.Prime] : moritaGamma p 1 = -1 := by simp

example : moritaGamma 3 ((2 : ℕ) : ℤ_[3]) = 1 := by
  rw [moritaGamma_natCast]
  simp [moritaGammaNat, Finset.prod_filter, Finset.prod_range_succ]

example : moritaGamma 3 ((3 : ℕ) : ℤ_[3]) = -2 := by
  rw [moritaGamma_natCast]
  simp [moritaGammaNat, Finset.prod_filter, Finset.prod_range_succ]
  norm_num

example : moritaGamma 3 ((4 : ℕ) : ℤ_[3]) = 2 := by
  rw [moritaGamma_natCast]
  simp [moritaGammaNat, Finset.prod_filter, Finset.prod_range_succ]
  norm_num

example : moritaGamma 3 ((5 : ℕ) : ℤ_[3]) = -8 := by
  rw [moritaGamma_natCast]
  simp [moritaGammaNat, Finset.prod_filter, Finset.prod_range_succ]
  norm_num

example : moritaGamma 5 ((3 : ℕ) : ℤ_[5]) = -2 := by
  rw [moritaGamma_natCast]
  simp [moritaGammaNat, Finset.prod_filter, Finset.prod_range_succ]
  norm_num

example : moritaGamma 5 ((4 : ℕ) : ℤ_[5]) = 6 := by
  rw [moritaGamma_natCast]
  simp [moritaGammaNat, Finset.prod_filter, Finset.prod_range_succ]
  norm_num

example : moritaGamma 5 ((5 : ℕ) : ℤ_[5]) = -24 := by
  rw [moritaGamma_natCast]
  simp [moritaGammaNat, Finset.prod_filter, Finset.prod_range_succ]
  norm_num

/-- At `p = 2` only odd factors contribute: `Γ_2(4) = 1 · 3`. -/
example : moritaGamma 2 ((4 : ℕ) : ℤ_[2]) = 3 := by
  rw [moritaGamma_natCast]
  simp [moritaGammaNat, Finset.prod_filter, Finset.prod_range_succ]
  norm_num

/-! ### Functional equation and values at negative integers -/

/-- `Γ_p(-1) = 1` for every prime, from `Γ_p(0) = -(-1) Γ_p(-1)`. -/
example (p : ℕ) [Fact p.Prime] : moritaGamma p (-1) = 1 := by
  have h := moritaGamma_add_one (p := p) (-1)
  simp only [neg_add_cancel, moritaGamma_zero, norm_neg, norm_one, ↓reduceIte, neg_neg,
    one_mul] at h
  exact h.symm

/-- The functional equation at a non-unit: `Γ_3(4) = -Γ_3(3)`. -/
example : moritaGamma 3 ((3 : ℕ) + 1 : ℤ_[3]) = -moritaGamma 3 (3 : ℕ) := by
  rw [moritaGamma_add_one, ite_eq_right (by rw [PadicInt.norm_p]; norm_num), neg_one_mul]

/-- `Γ_3(-3) Γ_3(4) = (-1) ^ (1 + 3 + 1) = -1`. -/
example : moritaGamma 3 (-((3 : ℕ) : ℤ_[3])) * moritaGamma 3 ((3 : ℕ) + 1) = -1 := by
  rw [moritaGamma_neg_natCast_mul_moritaGamma_natCast_add_one]
  norm_num

/-! ### Reflection formula -/

/-- `Γ_3(0) Γ_3(1) = (-1) ^ 3 = -1`. -/
example : moritaGamma 3 0 * moritaGamma 3 (1 - 0) = -1 := by
  rw [moritaGamma_mul_moritaGamma_one_sub (by decide)]
  simp only [map_zero, ↓reduceIte]
  norm_num

/-- `Γ_3(2) Γ_3(-1) = (-1) ^ 2 = 1`. -/
example : moritaGamma 3 2 * moritaGamma 3 (1 - 2) = 1 := by
  rw [moritaGamma_mul_moritaGamma_one_sub (by decide)]
  have h : PadicInt.toZMod (2 : ℤ_[3]) = 2 := map_ofNat _ 2
  have h0 : (2 : ZMod 3) ≠ 0 := by decide
  have hv : ZMod.val (2 : ZMod 3) = 2 := rfl
  rw [h, ite_eq_right h0, hv]
  norm_num

/-- The odd-prime hypothesis of the reflection formula is necessary: at `p = 2`,
`Γ_2(0) Γ_2(1) = -1`, while the right-hand side would be `(-1) ^ 2 = 1`. -/
example : ¬ (moritaGamma 2 0 * moritaGamma 2 (1 - 0) =
    (-1) ^ (if PadicInt.toZMod (0 : ℤ_[2]) = 0 then 2 else (PadicInt.toZMod (0 : ℤ_[2])).val)) := by
  simp only [moritaGamma_zero, sub_zero, moritaGamma_one, map_zero, ↓reduceIte, one_mul]
  intro h
  have := congrArg (fun x : ℤ_[2] => ‖x‖ < 1) h
  have h2 : (-1 : ℤ_[2]) - 1 = 0 := by rw [h]; norm_num
  have h3 : ‖(-2 : ℤ_[2])‖ = 2⁻¹ := by
    rw [norm_neg]; simpa using PadicInt.norm_p (p := 2)
  rw [show (-1 : ℤ_[2]) - 1 = -2 by ring] at h2
  rw [h2, norm_zero] at h3
  norm_num at h3

/-- `1/2` exists in `ℤ_[3]`, so the hypothesis of `moritaGamma_sq_of_two_mul_eq_one` can be met. -/
example : ∃ x : ℤ_[3], 2 * x = 1 := by
  have hu : IsUnit (2 : ℤ_[3]) := by
    rw [PadicInt.isUnit_iff]
    have := PadicInt.norm_natCast_eq_one_iff (p := 3) (n := 2)
    simpa using this.mpr (by decide)
  obtain ⟨u, hu⟩ := hu
  exact ⟨↑u⁻¹, by rw [← hu, Units.mul_inv]⟩

/-- `Γ_3(1/2) ^ 2 = 1` since `3 ≡ 3 (mod 4)`. -/
example (x : ℤ_[3]) (hx : 2 * x = 1) : moritaGamma 3 x ^ 2 = 1 := by
  rw [moritaGamma_sq_of_two_mul_eq_one (by decide) hx]
  rfl

/-- `Γ_5(1/2) ^ 2 = -1` since `5 ≡ 1 (mod 4)`. -/
example (x : ℤ_[5]) (hx : 2 * x = 1) : moritaGamma 5 x ^ 2 = -1 := by
  rw [moritaGamma_sq_of_two_mul_eq_one (by decide) hx]
  rfl

/-! ### Congruences and continuity -/

/-- `Γ_3(4) ≡ Γ_3(1) (mod 3)`. -/
example : PadicInt.toZModPow 1 (moritaGammaNat 3 (1 + 3 ^ 1)) =
    PadicInt.toZModPow 1 (moritaGammaNat 3 1) :=
  toZModPow_moritaGammaNat_add_prime_pow (Or.inl (by decide)) 1

/-- At `p = 2` the congruence holds modulo `2 ^ 3`: `Γ_2(8) ≡ Γ_2(0) (mod 8)`. -/
example : ‖moritaGammaNat 2 8 - moritaGammaNat 2 0‖ ≤ (2 : ℝ) ^ (-(3 : ℤ)) :=
  norm_moritaGammaNat_sub_le (Or.inr le_rfl) (by decide)

/-- The restriction `3 ≤ s` at `p = 2` is needed: `Γ_2(4) = 3 ≢ 1 = Γ_2(0) (mod 4)`. -/
example : ¬ ‖moritaGammaNat 2 4 - moritaGammaNat 2 0‖ ≤ (2 : ℝ) ^ (-(2 : ℤ)) := by
  have h4 : moritaGammaNat 2 4 = 3 := by
    simp [moritaGammaNat, Finset.prod_filter, Finset.prod_range_succ]
    norm_num
  rw [h4, moritaGammaNat_zero, show (3 : ℤ_[2]) - 1 = ((2 : ℕ) : ℤ_[2]) by norm_num,
    PadicInt.norm_p]
  norm_num

/-- `Γ_p` is unit-valued. -/
example (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) : IsUnit (moritaGamma p x) := isUnit_moritaGamma x

/-! ### Existence and uniqueness, including `p = 2` -/

example : ∃! Γ : C(ℤ_[2], ℤ_[2]), IsMoritaPadicGamma 2 Γ := existsUnique_isMoritaPadicGamma 2

example : IsMoritaPadicGamma 5 (moritaGamma 5) := isMoritaPadicGamma_moritaGamma 5

/-- The interpolation criterion applied to a constant sequence. -/
example (p : ℕ) [Fact p.Prime] (c : ℤ_[p]) : ∃! f : C(ℤ_[p], ℤ_[p]), ∀ k : ℕ, f k = c :=
  PadicInt.existsUnique_continuous_natCast_eq (fun _ => c) fun _ => ⟨0, fun _ _ _ => by simp⟩

/-- A non-example for `IsMoritaPadicGamma`: the constant function `1` (it fails at `n = 1`). -/
example (p : ℕ) [Fact p.Prime] : ¬ IsMoritaPadicGamma p (ContinuousMap.const _ 1) := by
  intro h
  have := h.natCast_eq (n := 1) one_pos
  simp [moritaGammaNat, Finset.filter_singleton] at this
  exact two_ne_zero (by linear_combination this : (2 : ℤ_[p]) = 0)
