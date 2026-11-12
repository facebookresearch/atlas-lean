/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! # Negligible functions: closure lemmas

A negligible function decays faster than every inverse
polynomial. Negligible functions are closed under addition,
constant multiples, and multiplication by polynomially bounded
functions. This is the asymptotic-security core of roadmap
package QCI-19 of the Atlas TCS canon roadmap.

Source: Katz and Lindell, Introduction to Modern Cryptography
(3rd ed.), Section 3.1.2.
-/

/-- A function `f : ℕ → ℝ` is negligible if it decays faster than
every inverse polynomial: for every `c`, eventually
`|f n| ≤ 1 / n ^ c` (with the real power convention through
natural exponentiation). -/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |f n| ≤ 1 / (n : ℝ) ^ c

/-- The constant zero function is negligible, and negligible
functions are closed under addition and under multiplication by
a polynomially bounded function: if `|g n| ≤ n ^ d` eventually
and `f` is negligible, then `fun n => g n * f n` is negligible. -/
theorem negligible_add {f g : ℕ → ℝ} (hf : Negligible f) (hg : Negligible g) :
    Negligible (fun n => f n + g n) := by
  intro c
  obtain ⟨Nf, hf'⟩ := hf (c + 1)
  obtain ⟨Ng, hg'⟩ := hg (c + 1)
  refine ⟨max (max Nf Ng) 2, fun n hn => ?_⟩
  have hnNf : Nf ≤ n :=
    le_trans (le_max_left Nf Ng) (le_trans (le_max_left (max Nf Ng) 2) hn)
  have hnNg : Ng ≤ n :=
    le_trans (le_max_right Nf Ng) (le_trans (le_max_left (max Nf Ng) 2) hn)
  have hn2 : 2 ≤ n := le_trans (le_max_right (max Nf Ng) 2) hn
  have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le two_pos hn2r
  have h1 : |f n| ≤ 1 / (n : ℝ) ^ (c + 1) := hf' n hnNf
  have h2 : |g n| ≤ 1 / (n : ℝ) ^ (c + 1) := hg' n hnNg
  have hpowc : (0 : ℝ) < (n : ℝ) ^ c := pow_pos hnpos _
  have h2n : (2 : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hnpos).mpr hn2r
  have hnn : (0 : ℝ) ≤ 1 / (n : ℝ) ^ c := le_of_lt (one_div_pos.mpr hpowc)
  have hsplit : (n : ℝ) ^ (c + 1) = (n : ℝ) ^ c * (n : ℝ) := pow_succ _ _
  have hkey : (2 : ℝ) / (n : ℝ) ^ (c + 1) ≤ 1 / (n : ℝ) ^ c := by
    rw [hsplit]
    have hfield : (2 : ℝ) / ((n : ℝ) ^ c * (n : ℝ))
        = ((2 : ℝ) / (n : ℝ)) * (1 / (n : ℝ) ^ c) := by ring
    rw [hfield]
    calc ((2 : ℝ) / (n : ℝ)) * (1 / (n : ℝ) ^ c)
          ≤ 1 * (1 / (n : ℝ) ^ c) := mul_le_mul_of_nonneg_right h2n hnn
      _ = 1 / (n : ℝ) ^ c := one_mul _
  calc |f n + g n| ≤ |f n| + |g n| := abs_add_le _ _
    _ ≤ 1 / (n : ℝ) ^ (c + 1) + 1 / (n : ℝ) ^ (c + 1) := add_le_add h1 h2
    _ = 2 / (n : ℝ) ^ (c + 1) := by ring
    _ ≤ 1 / (n : ℝ) ^ c := hkey

theorem negligible_const_mul {f : ℕ → ℝ} (hf : Negligible f) (c : ℝ) :
    Negligible (fun n => c * f n) := by
  intro e
  obtain ⟨Nf, hf'⟩ := hf (e + 1)
  obtain ⟨M, hM⟩ := exists_nat_ge |c|
  refine ⟨max (max Nf M) 1, fun n hn => ?_⟩
  have hnNf : Nf ≤ n :=
    le_trans (le_max_left Nf M) (le_trans (le_max_left (max Nf M) 1) hn)
  have hnM : M ≤ n :=
    le_trans (le_max_right Nf M) (le_trans (le_max_left (max Nf M) 1) hn)
  have hn1 : 1 ≤ n := le_trans (le_max_right (max Nf M) 1) hn
  have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1r
  have hcn : |c| ≤ (n : ℝ) := le_trans hM (by exact_mod_cast hnM)
  have h1 : |f n| ≤ 1 / (n : ℝ) ^ (e + 1) := hf' n hnNf
  have hpowe : (0 : ℝ) < (n : ℝ) ^ e := pow_pos hnpos _
  have hcn1 : |c| / (n : ℝ) ≤ 1 := (div_le_one hnpos).mpr hcn
  have hnn : (0 : ℝ) ≤ 1 / (n : ℝ) ^ e := le_of_lt (one_div_pos.mpr hpowe)
  have hsplit : (n : ℝ) ^ (e + 1) = (n : ℝ) ^ e * (n : ℝ) := pow_succ _ _
  have hkey : |c| / (n : ℝ) ^ (e + 1) ≤ 1 / (n : ℝ) ^ e := by
    rw [hsplit]
    have hfield : |c| / ((n : ℝ) ^ e * (n : ℝ))
        = (|c| / (n : ℝ)) * (1 / (n : ℝ) ^ e) := by ring
    rw [hfield]
    calc (|c| / (n : ℝ)) * (1 / (n : ℝ) ^ e)
          ≤ 1 * (1 / (n : ℝ) ^ e) := mul_le_mul_of_nonneg_right hcn1 hnn
      _ = 1 / (n : ℝ) ^ e := one_mul _
  calc |c * f n| = |c| * |f n| := abs_mul _ _
    _ ≤ |c| * (1 / (n : ℝ) ^ (e + 1)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |c| / (n : ℝ) ^ (e + 1) := by ring
    _ ≤ 1 / (n : ℝ) ^ e := hkey

theorem negligible_mul_of_poly_bound {f g : ℕ → ℝ} (hf : Negligible f)
    {d : ℕ} (hg : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |g n| ≤ (n : ℝ) ^ d) :
    Negligible (fun n => g n * f n) := by
  intro e
  obtain ⟨Nf, hf'⟩ := hf (e + d)
  obtain ⟨Ng, hg'⟩ := hg
  refine ⟨max (max Nf Ng) 1, fun n hn => ?_⟩
  have hnNf : Nf ≤ n :=
    le_trans (le_max_left Nf Ng) (le_trans (le_max_left (max Nf Ng) 1) hn)
  have hnNg : Ng ≤ n :=
    le_trans (le_max_right Nf Ng) (le_trans (le_max_left (max Nf Ng) 1) hn)
  have hn1 : 1 ≤ n := le_trans (le_max_right (max Nf Ng) 1) hn
  have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1r
  have h1 : |f n| ≤ 1 / (n : ℝ) ^ (e + d) := hf' n hnNf
  have h2 : |g n| ≤ (n : ℝ) ^ d := hg' n hnNg
  have hsplit : (n : ℝ) ^ (e + d) = (n : ℝ) ^ e * (n : ℝ) ^ d := pow_add _ _ _
  have hne : (n : ℝ) ^ e ≠ 0 := ne_of_gt (pow_pos hnpos _)
  have hnd : (n : ℝ) ^ d ≠ 0 := ne_of_gt (pow_pos hnpos _)
  calc |g n * f n| = |g n| * |f n| := abs_mul _ _
    _ ≤ (n : ℝ) ^ d * (1 / (n : ℝ) ^ (e + d)) :=
        mul_le_mul h2 h1 (abs_nonneg _) (pow_nonneg (le_of_lt hnpos) _)
    _ = 1 / (n : ℝ) ^ e := by rw [hsplit]; field_simp
