/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.JohnsonBound

/-!
# Tests: the q-ary Johnson bound
-/

@[expose] public section

namespace MathlibExtTest.Combinatorics.Coding.JohnsonBound

set_option autoImplicit false

open Finset MathlibExt.Combinatorics.Coding.ListDecoding
  MathlibExt.Combinatorics.Coding.JohnsonBound

#print axioms qary_johnson_bound
#print axioms isListDecodable_of_lt_johnsonRadius
#print axioms not_isListDecodable_weightCode_three

/-- The binary repetition code of length 3. -/
def rep3 : Finset (Fin 3 → Bool) := {fun _ => false, fun _ => true}

theorem rep3_dist : ∀ c₁ ∈ rep3, ∀ c₂ ∈ rep3, c₁ ≠ c₂ → 3 ≤ hammingDist c₁ c₂ := by
  decide

/-- Binary instance of the q-ary bound on the repetition code. -/
theorem rep3_list_decodable : IsListDecodable rep3 1 (2 * 3 * 3) := by
  have hcard : Fintype.card Bool = 2 := Fintype.card_bool
  have hq : 2 ≤ Fintype.card Bool := by omega
  have hqe : Fintype.card Bool * 1 ≤ (Fintype.card Bool - 1) * 3 := by omega
  have hJ : ((Fintype.card Bool : ℤ) - 1) * 3 * ((3 : ℤ) - 3) <
      ((Fintype.card Bool : ℤ) - 1) * ((3 : ℤ) - 1) ^ 2 + (1 : ℤ) ^ 2 := by
    rw [hcard]
    decide
  have h := isListDecodable_of_qary_johnson (C := rep3) (d := 3) (e := 1)
    hq hqe rep3_dist hJ
  rw [hcard] at h
  exact h

/-- The ternary repetition code of length 6. -/
def rep6 : Finset (Fin 6 → Fin 3) := {fun _ => 0, fun _ => 1, fun _ => 2}

theorem rep6_dist : ∀ c₁ ∈ rep6, ∀ c₂ ∈ rep6, c₁ ≠ c₂ → 6 ≤ hammingDist c₁ c₂ := by
  intro c₁ hc₁ c₂ hc₂ hne
  simp only [rep6, Finset.mem_insert, Finset.mem_singleton] at hc₁ hc₂
  rcases hc₁ with rfl | rfl | rfl <;> rcases hc₂ with rfl | rfl | rfl
  · exact absurd rfl hne
  · decide
  · decide
  · decide
  · exact absurd rfl hne
  · decide
  · decide
  · decide
  · exact absurd rfl hne

/-- A `q = 3` instance of the q-ary bound. -/
theorem rep6_list_decodable : IsListDecodable rep6 3 (3 * 6 * 6) := by
  have hcard : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
  have hq : 2 ≤ Fintype.card (Fin 3) := by omega
  have hqe : Fintype.card (Fin 3) * 3 ≤ (Fintype.card (Fin 3) - 1) * 6 := by omega
  have hJ : ((Fintype.card (Fin 3) : ℤ) - 1) * 6 * ((6 : ℤ) - 6) <
      ((Fintype.card (Fin 3) : ℤ) - 1) * ((6 : ℤ) - 3) ^ 2 + (3 : ℤ) ^ 2 := by
    rw [hcard]
    decide
  have h := isListDecodable_of_qary_johnson (C := rep6) (d := 6) (e := 3)
    hq hqe rep6_dist hJ
  rw [hcard] at h
  exact h

/-- The real Johnson radius at `n = 20`, `d = 8` exceeds radius `5`. -/
theorem johnsonRadius_two_example : (5 : ℝ) < johnsonRadius 2 ((8 : ℝ) / 20) * 20 := by
  have e1 : (1 : ℝ) - 1 / ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
  have e2inner : (1 : ℝ) - ((2 : ℕ) : ℝ) * ((8 : ℝ) / 20) / (((2 : ℕ) : ℝ) - 1) = 1 / 5 := by
    norm_num
  have e2 : max (0 : ℝ) (1 - ((2 : ℕ) : ℝ) * ((8 : ℝ) / 20) / (((2 : ℕ) : ℝ) - 1)) = 1 / 5 := by
    rw [e2inner, max_eq_right (show (0 : ℝ) ≤ 1 / 5 by norm_num)]
  have hJ : johnsonRadius 2 ((8 : ℝ) / 20) = (1 / 2) * (1 - Real.sqrt (1 / 5)) := by
    have hrfl : johnsonRadius 2 ((8 : ℝ) / 20) =
        (1 - 1 / ((2 : ℕ) : ℝ)) *
          (1 - Real.sqrt (max 0 (1 - ((2 : ℕ) : ℝ) * ((8 : ℝ) / 20) / (((2 : ℕ) : ℝ) - 1)))) := rfl
    rw [hrfl, e1, e2]
  rw [hJ]
  have hpos : (0 : ℝ) < 1 / 2 := by norm_num
  have hsqrt : Real.sqrt ((1 : ℝ) / 5) < 1 / 2 := by
    rw [Real.sqrt_lt' hpos]
    norm_num
  linarith [hsqrt]

/-- The explicitly clipped Johnson-radius extension at `q = 2`, `δ = 1`, outside
the classical Johnson-radius domain: the unclipped square-root argument is `-1`,
clipped to `0`. -/
theorem rep3_johnsonRadius_value : johnsonRadius 2 ((3 : ℝ) / 3) = 1 / 2 := by
  have e1 : (1 : ℝ) - 1 / ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
  have earg : (1 : ℝ) - ((2 : ℕ) : ℝ) * ((3 : ℝ) / 3) / (((2 : ℕ) : ℝ) - 1) = -1 := by
    norm_num
  have eclip : max (0 : ℝ) (1 - ((2 : ℕ) : ℝ) * ((3 : ℝ) / 3) / (((2 : ℕ) : ℝ) - 1)) = 0 := by
    rw [earg, max_eq_left (show (-1 : ℝ) ≤ 0 by norm_num)]
  have hsqrt : Real.sqrt (0 : ℝ) = 0 := Real.sqrt_zero
  have hrfl : johnsonRadius 2 ((3 : ℝ) / 3) =
      (1 - 1 / ((2 : ℕ) : ℝ)) *
        (1 - Real.sqrt (max 0 (1 - ((2 : ℕ) : ℝ) * ((3 : ℝ) / 3) / (((2 : ℕ) : ℝ) - 1)))) := rfl
  rw [hrfl, e1, eclip, hsqrt]
  norm_num

/-- Radius `1` is below the explicitly clipped Johnson-radius extension at `q = 2`,
`n = 3`, `d = 3` (`δ = 1`), outside the classical Johnson-radius domain. -/
theorem rep3_one_lt_johnsonRadius_mul :
    (1 : ℝ) < johnsonRadius 2 ((3 : ℝ) / 3) * 3 := by
  rw [rep3_johnsonRadius_value]
  norm_num

/-- The integer Johnson conditions at `q = 2`, `n = 3`, `d = 3`, `e = 1`, through
the explicitly clipped extension at `δ = 1`, outside the classical
Johnson-radius domain. -/
theorem rep3_johnson_conditions :
    2 * 1 < (2 - 1) * 3 ∧
      ((2 : ℤ) - 1) * 3 * ((3 : ℤ) - 3) <
        ((2 : ℤ) - 1) * ((3 : ℤ) - 1) ^ 2 + (1 : ℤ) ^ 2 := by
  have he : ((1 : ℕ) : ℝ) <
      johnsonRadius 2 (((3 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) * ((3 : ℕ) : ℝ) := by
    simpa using rep3_one_lt_johnsonRadius_mul
  exact qary_johnson_conditions_of_lt_johnsonRadius (q := 2) (n := 3) (d := 3) (e := 1)
    (by norm_num) he

/-- Binary instance of the bound on the repetition code, through the explicitly
clipped extension at `δ = 1`, outside the classical Johnson-radius domain. -/
theorem rep3_list_decodable_of_real_radius : IsListDecodable rep3 1 (2 * 3 * 3) := by
  have hcard : Fintype.card Bool = 2 := Fintype.card_bool
  have hq : 2 ≤ Fintype.card Bool := by omega
  have he : ((1 : ℕ) : ℝ) < johnsonRadius (Fintype.card Bool) (((3 : ℕ) : ℝ) /
      ((3 : ℕ) : ℝ)) * ((3 : ℕ) : ℝ) := by
    rw [hcard]
    simpa using rep3_one_lt_johnsonRadius_mul
  have h := isListDecodable_of_lt_johnsonRadius (C := rep3) (d := 3) (e := 1)
    hq rep3_dist he
  rw [hcard] at h
  exact h

/-- Binary instance on the repetition code, through the floor-radius bridge at
`ρ = 1 / 3` over the explicitly clipped extension at `δ = 1`, outside the
classical Johnson-radius domain. -/
theorem rep3_list_decodable_of_floor_radius : IsListDecodable rep3 1 (2 * 3 * 3) := by
  have hcard : Fintype.card Bool = 2 := Fintype.card_bool
  have hq : 2 ≤ Fintype.card Bool := by omega
  have hρ0 : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have hρ : (1 / 3 : ℝ) <
      johnsonRadius (Fintype.card Bool) (((3 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) := by
    rw [hcard]
    have hj : johnsonRadius 2 (((3 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = 1 / 2 := by
      simpa using rep3_johnsonRadius_value
    rw [hj]
    norm_num
  have h := isListDecodable_floor_of_lt_johnsonRadius (C := rep3) (d := 3) (ρ := 1 / 3)
    hq rep3_dist hρ0 hρ
  rw [hcard] at h
  have hfloor : Nat.floor ((1 / 3 : ℝ) * ((3 : ℕ) : ℝ)) = 1 := by
    rw [show (1 / 3 : ℝ) * ((3 : ℕ) : ℝ) = 1 by norm_num]
    exact Nat.floor_one
  rw [hfloor] at h
  exact h

/-- There are `35` binary words of length `7` and weight `3`. -/
theorem weightCode_three_card_seven : (weightCode 7 3).card = 35 := by
  decide

end MathlibExtTest.Combinatorics.Coding.JohnsonBound
