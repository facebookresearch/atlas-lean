/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import MathlibExt.Analysis.SpecialFunctions.ExponentialIntegral.Ei

@[expose] public section

namespace MathlibExtTest.Analysis.SpecialFunctions.ExponentialIntegral.Ei

open MetaMathlibExt

-- Analysis 385: Real Exponential Integral

theorem realExponentialIntegral_one_mem_Ioo :
    realExponentialIntegral 1 ∈ Set.Ioo 1 2 := by
  have hpow_nat :
      ∀ k : ℕ,
        4 ^ k ≤ (k + 1) * Nat.factorial (k + 1) := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k ih =>
        have hfact :
            Nat.factorial (k + 1 + 1) =
              (k + 1 + 1) * Nat.factorial (k + 1) :=
          Nat.factorial_succ _
        have hsq :
            (k + 1 + 1) * (k + 1 + 1) =
              k * k + 4 * (k + 1) := by
          ring
        have hle :
            4 * (k + 1) ≤
              (k + 1 + 1) * (k + 1 + 1) := by
          rw [hsq]
          exact Nat.le_add_left _ _
        calc
          4 ^ (k + 1) = 4 * 4 ^ k := by ring
          _ ≤ 4 * ((k + 1) * Nat.factorial (k + 1)) := by
            gcongr
          _ = (4 * (k + 1)) * Nat.factorial (k + 1) := by
            ring
          _ ≤ ((k + 1 + 1) * (k + 1 + 1)) *
                Nat.factorial (k + 1) := by
            gcongr
          _ = (k + 1 + 1) *
                ((k + 1 + 1) * Nat.factorial (k + 1)) := by
            ring
          _ = (k + 1 + 1) * Nat.factorial (k + 1 + 1) := by
            rw [hfact]

  have hpow_real :
      ∀ k : ℕ,
        (4 : ℝ) ^ k ≤
          ((k : ℝ) + 1) *
            (Nat.factorial (k + 1) : ℝ) := by
    intro k
    have hnat :
        4 ^ k ≤ (k + 1) * Nat.factorial (k + 1) :=
      hpow_nat k
    have hcast :
        ((4 ^ k : ℕ) : ℝ) ≤
          (((k + 1) * Nat.factorial (k + 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hcast ⊢
    linarith [hcast]

  have hpos_denom :
      ∀ k : ℕ,
        0 <
          ((k : ℝ) + 1) *
            (Nat.factorial (k + 1) : ℝ) := by
    intro k
    apply mul_pos
    · have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith
    · exact_mod_cast Nat.factorial_pos _

  have h_nonneg :
      ∀ k : ℕ,
        0 ≤
          (1 : ℝ) /
            (((k : ℝ) + 1) *
              (Nat.factorial (k + 1) : ℝ)) := by
    intro k
    apply div_nonneg zero_le_one
    exact le_of_lt (hpos_denom k)

  have h_le :
      ∀ k : ℕ,
        (1 : ℝ) /
            (((k : ℝ) + 1) *
              (Nat.factorial (k + 1) : ℝ))
          ≤ (1 / 4 : ℝ) ^ k := by
    intro k
    have h4pos : 0 < (4 : ℝ) ^ k := by
      positivity
    have hpow := hpow_real k
    have h1 :
        (1 : ℝ) /
            (((k : ℝ) + 1) *
              (Nat.factorial (k + 1) : ℝ))
          ≤ 1 / (4 : ℝ) ^ k :=
      one_div_le_one_div_of_le h4pos hpow
    have heq :
        (1 / 4 : ℝ) ^ k =
          1 / (4 : ℝ) ^ k := by
      rw [div_pow, one_pow]
    rw [heq]
    exact h1

  have hfact3 : Nat.factorial 3 = 6 := rfl

  have h_strict :
      (fun k : ℕ =>
        (1 : ℝ) /
          (((k : ℝ) + 1) *
            (Nat.factorial (k + 1) : ℝ))) 2
        <
      (fun k : ℕ => (1 / 4 : ℝ) ^ k) 2 := by
    change
      (1 : ℝ) /
          ((((2 : ℕ) : ℝ) + 1) *
            (Nat.factorial (2 + 1) : ℝ))
        <
      (1 / 4 : ℝ) ^ 2
    rw [show (2 : ℕ) + 1 = 3 from rfl, hfact3]
    norm_num

  have hg :
      Summable (fun k : ℕ => (1 / 4 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)

  have hf :
      Summable
        (fun k : ℕ =>
          (1 : ℝ) /
            (((k : ℝ) + 1) *
              (Nat.factorial (k + 1) : ℝ))) :=
    Summable.of_nonneg_of_le h_nonneg h_le hg

  have h_lt :
      (∑' k : ℕ,
        (1 : ℝ) /
          (((k : ℝ) + 1) *
            (Nat.factorial (k + 1) : ℝ)))
        <
      ∑' k : ℕ, (1 / 4 : ℝ) ^ k :=
    Summable.tsum_lt_tsum_of_nonneg
      h_nonneg h_le h_strict hg

  have h_geo :
      (∑' k : ℕ, (1 / 4 : ℝ) ^ k) = 4 / 3 := by
    have h :=
      tsum_geometric_of_lt_one
        (r := (1 / 4 : ℝ))
        (by norm_num)
        (by norm_num)
    rw [h]
    norm_num

  have h_upper :
      (∑' k : ℕ,
        (1 : ℝ) /
          (((k : ℝ) + 1) *
            (Nat.factorial (k + 1) : ℝ)))
        < 4 / 3 := by
    rw [h_geo] at h_lt
    exact h_lt

  have hfact1 : Nat.factorial 1 = 1 := rfl

  have h0 :
      (fun k : ℕ =>
        (1 : ℝ) /
          (((k : ℝ) + 1) *
            (Nat.factorial (k + 1) : ℝ))) 0 = 1 := by
    change
      (1 : ℝ) /
          ((((0 : ℕ) : ℝ) + 1) *
            (Nat.factorial (0 + 1) : ℝ))
        = 1
    rw [show (0 : ℕ) + 1 = 1 from rfl, hfact1]
    norm_num

  have h_lower :
      1 ≤
        ∑' k : ℕ,
          (1 : ℝ) /
            (((k : ℝ) + 1) *
              (Nat.factorial (k + 1) : ℝ)) := by
    have hle := hf.le_tsum 0 (fun j _ => h_nonneg j)
    simpa [h0] using hle

  simp only
    [realExponentialIntegral, Real.log_one, add_zero,
      one_pow, Set.mem_Ioo]

  have h_gamma_lower :
      1 / 2 < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant

  have h_gamma_upper :
      Real.eulerMascheroniConstant < 2 / 3 :=
    Real.eulerMascheroniConstant_lt_two_thirds

  constructor
  · linarith [h_gamma_lower, h_lower]
  · linarith [h_gamma_upper, h_upper]

end MathlibExtTest.Analysis.SpecialFunctions.ExponentialIntegral.Ei

end
