/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.RationalFunctionFareyPathPolyContFractOfFareyPath
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

namespace MathlibExtTest.Algebra.RationalFunctionFareyPathPolyContFractOfFareyPath

open MetaMathlibExt Polynomial

private noncomputable def sampleDen : ℕ → ℚ[X]
  | 0 => 1
  | 1 => X
  | 2 => X ^ 2 + 1
  | 3 => X ^ 3
  | 4 => X ^ 4 + X ^ 2 + 1
  | _ => 0

private noncomputable def sampleNum : ℕ → ℚ[X]
  | 0 => 0
  | 1 => C 2
  | 2 => C 2 * X
  | 3 => C 2 * X ^ 2 - C 2
  | 4 => C 2 * X ^ 3
  | _ => 0

private noncomputable def sampleC : ℕ → ℚ
  | 1 => 2
  | 2 => -2
  | 3 => -2
  | 4 => 2
  | _ => 0

private noncomputable def sampleQuot : ℕ → ℚ[X]
  | 0 => 0
  | 1 => C ((sampleC 1)⁻¹) * sampleDen 1
  | 2 => -C ((sampleC 2)⁻¹ * sampleC 1) * (sampleNum 2 * sampleDen 0 - sampleNum 0 * sampleDen 2)
  | 3 => C ((-1) ^ (3 + 1) * (sampleC 3)⁻¹ * sampleC 2 *
      ∏ j ∈ Finset.Icc 1 (3 - 2), sampleC j ^ (2 * (-1 : ℤ) ^ (3 - j + 1))) *
      (sampleNum 3 * sampleDen 1 - sampleNum 1 * sampleDen 3)
  | 4 => C ((-1) ^ (4 + 1) * (sampleC 4)⁻¹ * sampleC 3 *
      ∏ j ∈ Finset.Icc 1 (4 - 2), sampleC j ^ (2 * (-1 : ℤ) ^ (4 - j + 1))) *
      (sampleNum 4 * sampleDen 2 - sampleNum 2 * sampleDen 4)
  | _ => 0

-- The partial quotients `a 1, …, a 4` are nonconstant (`a 0 = 0` is constant); the convergent
-- scalars are `t₁ = 1 / 2`, `t₂ = 1` (the sign `ε₂ = -1` cancels against `c₂ = -2`) and
-- `t₃ = -1 / 2` (a negative scalar); and the convergents match the path `u i / v i` for every
-- `i ≤ 4`.
example : (∀ i, 1 ≤ i → i ≤ 4 → 0 < (sampleQuot i).natDegree) ∧
    (polyContFract sampleQuot 4).nums 1 = algebraMap ℚ[X] (RatFunc ℚ) 1 ∧
    (polyContFract sampleQuot 4).dens 1 =
      algebraMap ℚ[X] (RatFunc ℚ) (C ((1 : ℚ) / 2) * X) ∧
    (polyContFract sampleQuot 4).nums 2 =
      algebraMap ℚ[X] (RatFunc ℚ) (C (2 : ℚ) * X) ∧
    (polyContFract sampleQuot 4).dens 2 =
      algebraMap ℚ[X] (RatFunc ℚ) (X ^ 2 + 1) ∧
    (polyContFract sampleQuot 4).nums 3 =
      algebraMap ℚ[X] (RatFunc ℚ) (-X ^ 2 + 1) ∧
    (polyContFract sampleQuot 4).dens 3 =
      algebraMap ℚ[X] (RatFunc ℚ) (C (-(1 : ℚ) / 2) * X ^ 3) ∧
    (polyContFract sampleQuot 4).convs 0 =
      algebraMap ℚ[X] (RatFunc ℚ) (sampleNum 0) / algebraMap ℚ[X] (RatFunc ℚ) (sampleDen 0) ∧
    (polyContFract sampleQuot 4).convs 1 =
      algebraMap ℚ[X] (RatFunc ℚ) (sampleNum 1) / algebraMap ℚ[X] (RatFunc ℚ) (sampleDen 1) ∧
    (polyContFract sampleQuot 4).convs 2 =
      algebraMap ℚ[X] (RatFunc ℚ) (sampleNum 2) / algebraMap ℚ[X] (RatFunc ℚ) (sampleDen 2) ∧
    (polyContFract sampleQuot 4).convs 3 =
      algebraMap ℚ[X] (RatFunc ℚ) (sampleNum 3) / algebraMap ℚ[X] (RatFunc ℚ) (sampleDen 3) ∧
    (polyContFract sampleQuot 4).convs 4 =
      algebraMap ℚ[X] (RatFunc ℚ) (sampleNum 4) / algebraMap ℚ[X] (RatFunc ℚ) (sampleDen 4) := by
  have hdegree (i : ℕ) (hi : i ≤ 4) : (sampleDen i).degree = i := by
    interval_cases i <;> norm_num [sampleDen] <;> compute_degree!
  have hdeg : ∀ i, 1 ≤ i → i ≤ 4 → (sampleDen (i - 1)).degree < (sampleDen i).degree := by
    intro i hi hin
    rw [hdegree (i - 1) (by omega), hdegree i hin]
    exact_mod_cast (show i - 1 < i by omega)
  have hc : ∀ i, 1 ≤ i → i ≤ 4 → sampleC i ≠ 0 := by
    intro i hi hin
    interval_cases i <;> norm_num [sampleC]
  have hdet : ∀ i, 1 ≤ i → i ≤ 4 →
      sampleNum i * sampleDen (i - 1) - sampleNum (i - 1) * sampleDen i = C (sampleC i) := by
    intro i hi hin
    interval_cases i <;> norm_num [sampleNum, sampleDen, sampleC] <;> ring
  have ha0 : sampleQuot 0 = sampleNum 0 := by rfl
  have ha1 : sampleQuot 1 = C (sampleC 1)⁻¹ * sampleDen 1 := by rfl
  have ha2 : sampleQuot 2 = -C ((sampleC 2)⁻¹ * sampleC 1) *
      (sampleNum 2 * sampleDen 0 - sampleNum 0 * sampleDen 2) := by rfl
  have ha : ∀ i, 3 ≤ i → i ≤ 4 →
      sampleQuot i = C ((-1) ^ (i + 1) * (sampleC i)⁻¹ * sampleC (i - 1) *
        ∏ j ∈ Finset.Icc 1 (i - 2), sampleC j ^ (2 * (-1 : ℤ) ^ (i - j + 1))) *
        (sampleNum i * sampleDen (i - 2) - sampleNum (i - 2) * sampleDen i) := by
    intro i hi hin
    interval_cases i <;> rfl
  obtain ⟨hpos, hconv⟩ := polyContFract_of_farey_path sampleNum sampleDen sampleC 4 rfl hc hdeg
    hdet sampleQuot ha0 ha1 ha2 ha
  obtain ⟨t1, ht1_eq, hn1, hd1, _⟩ := hconv 1 (by decide)
  have ht1 : t1 = (1 : ℚ) / 2 := by
    rw [ht1_eq]
    norm_num [sampleC]
  have hnums1 : (polyContFract sampleQuot 4).nums 1 = algebraMap ℚ[X] (RatFunc ℚ) 1 := by
    rw [hn1, ht1]
    congr 1
    norm_num [sampleNum]
    rw [← C_mul]
    norm_num
  have hdens1 : (polyContFract sampleQuot 4).dens 1 =
      algebraMap ℚ[X] (RatFunc ℚ) (C ((1 : ℚ) / 2) * X) := by
    rw [hd1, ht1]
    simp [sampleDen]
  obtain ⟨t2, ht2_eq, hn2, hd2, _⟩ := hconv 2 (by decide)
  have ht2 : t2 = 1 := by
    rw [ht2_eq]
    have h1 : (2 : ℕ) % 4 = 2 := by decide
    simp [h1]
    rw [Finset.prod_Icc_succ_top (by decide : 1 ≤ 1 + 1)]
    norm_num [sampleC]
  have hnums2 : (polyContFract sampleQuot 4).nums 2 =
      algebraMap ℚ[X] (RatFunc ℚ) (C (2 : ℚ) * X) := by
    rw [hn2, ht2]
    simp [sampleNum]
  have hdens2 : (polyContFract sampleQuot 4).dens 2 =
      algebraMap ℚ[X] (RatFunc ℚ) (X ^ 2 + 1) := by
    rw [hd2, ht2]
    simp [sampleDen]
  obtain ⟨t3, ht3_eq, hn3, hd3, _⟩ := hconv 3 (by decide)
  have ht3 : t3 = -(1 : ℚ) / 2 := by
    rw [ht3_eq, show Finset.Icc 1 3 = insert 1 (insert 2 {3}) by decide]
    norm_num [sampleC]
  have hnums3 : (polyContFract sampleQuot 4).nums 3 =
      algebraMap ℚ[X] (RatFunc ℚ) (-X ^ 2 + 1) := by
    rw [hn3, ht3]
    congr 1
    rw [sampleNum, mul_sub, ← mul_assoc, ← C_mul]
    norm_num
  have hdens3 : (polyContFract sampleQuot 4).dens 3 =
      algebraMap ℚ[X] (RatFunc ℚ) (C (-(1 : ℚ) / 2) * X ^ 3) := by
    rw [hd3, ht3]
    simp [sampleDen]
  refine ⟨hpos, hnums1, hdens1, hnums2, hdens2, hnums3, hdens3, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨_, _, _, _, hcvs⟩ := hconv 0 (Nat.zero_le 4)
    exact hcvs
  · obtain ⟨_, _, _, _, hcvs⟩ := hconv 1 (by decide)
    exact hcvs
  · obtain ⟨_, _, _, _, hcvs⟩ := hconv 2 (by decide)
    exact hcvs
  · obtain ⟨_, _, _, _, hcvs⟩ := hconv 3 (by decide)
    exact hcvs
  · obtain ⟨_, _, _, _, hcvs⟩ := hconv 4 le_rfl
    exact hcvs

end MathlibExtTest.Algebra.RationalFunctionFareyPathPolyContFractOfFareyPath
