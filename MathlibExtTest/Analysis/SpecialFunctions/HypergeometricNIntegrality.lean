/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.HypergeometricNIntegrality

import Mathlib.Tactic

@[expose] public section

namespace MetaMathlibExt.HypergeometricNIntegrality

example : pochhammerCoeff {1 / 2, 1 / 2} {1, 1} 2 = 9 / 64 := by
  norm_num [pochhammerCoeff, ascPochhammer]

example :
    MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient
        ((1 : ℚ) ::ₘ {1 / 2, 1 / 2}) ({1, 1} : Multiset ℚ) 2 = 9 / 64 := by
  rw [← pochhammerCoeff_eq_generalizedHypergeometricCoefficient]
  norm_num [pochhammerCoeff, ascPochhammer]

example : AdmissibleParams ({1 / 2, 1} : Multiset ℚ) := by
  intro t ht k h
  simp at ht
  have hk : (0 : ℚ) ≤ (k : ℚ) := by exact_mod_cast Nat.zero_le k
  rcases ht with rfl | rfl <;> linarith

example (n : ℕ) : (ascPochhammer ℚ n).eval (1 / 2 : ℚ) ≠ 0 := by
  apply ascPochhammer_eval_ne_zero_of_ne_neg_natCast
  intro k h
  have hk : (0 : ℚ) ≤ (k : ℚ) := by exact_mod_cast Nat.zero_le k
  linarith

example : modFract (5 / 2 : ℝ) = 1 / 2 := by
  have h : Int.fract (5 / 2 : ℝ) = 1 / 2 := by norm_num [Int.fract]
  rw [modFract, ite_eq_right (by rw [h]; norm_num), h]

example : modFract (2 : ℝ) = 1 := by
  have h : Int.fract (2 : ℝ) = 0 := by norm_num [Int.fract]
  rw [modFract, ite_eq_left h]

example : modFract (-1 / 2 : ℝ) = 1 / 2 := by
  have h : Int.fract (-1 / 2 : ℝ) = 1 / 2 := by norm_num [Int.fract]
  rw [modFract, ite_eq_right (by rw [h]; norm_num), h]

example : ChristolLE (3 / 2 : ℝ) (1 / 2 : ℝ) := by
  have h32 : modFract (3 / 2 : ℝ) = 1 / 2 := by
    have h : Int.fract (3 / 2 : ℝ) = 1 / 2 := by norm_num [Int.fract]
    rw [modFract, ite_eq_right (by rw [h]; norm_num), h]
  have h12 : modFract (1 / 2 : ℝ) = 1 / 2 := by
    have h : Int.fract (1 / 2 : ℝ) = 1 / 2 := by norm_num [Int.fract]
    rw [modFract, ite_eq_right (by rw [h]; norm_num), h]
  exact Or.inr ⟨by rw [h32, h12], by norm_num⟩

example : ¬ ChristolLE (1 / 2 : ℝ) (3 / 2 : ℝ) := by
  have h32 : modFract (3 / 2 : ℝ) = 1 / 2 := by
    have h : Int.fract (3 / 2 : ℝ) = 1 / 2 := by norm_num [Int.fract]
    rw [modFract, ite_eq_right (by rw [h]; norm_num), h]
  have h12 : modFract (1 / 2 : ℝ) = 1 / 2 := by
    have h : Int.fract (1 / 2 : ℝ) = 1 / 2 := by norm_num [Int.fract]
    rw [modFract, ite_eq_right (by rw [h]; norm_num), h]
  intro h
  unfold ChristolLE at h
  rw [h12, h32] at h
  rcases h with h | ⟨-, h⟩ <;> norm_num at h

example : christolXi {1 / 2, 1 / 2} {1, 1} 1 (1 / 2 : ℝ) = 2 := by
  simp [christolXi, ChristolLE, modFract, Multiset.filter_singleton]
  norm_num [Int.fract]

example : paramDenLcm {1 / 2, 1 / 2} {1, 1} = 2 := by
  unfold paramDenLcm
  rw [Multiset.map_add]
  norm_num [Multiset.map_cons, Multiset.lcm_cons, Multiset.cons_add]

example : paramDenLcm {1 / 2, 1 / 3} {1} = 6 := by
  unfold paramDenLcm
  rw [Multiset.map_add]
  norm_num [Multiset.map_cons, Multiset.lcm_cons, Multiset.cons_add]
  decide

example : lambda {1 / 2, 1 / 2} {1, 1} 2 = -2 := by
  norm_num [lambda, Multiset.filter_singleton]

example : baseConstant {1 / 2, 1 / 2} {1, 1} = 16 := by
  have hd : paramDenLcm {1 / 2, 1 / 2} {1, 1} = 2 := by
    unfold paramDenLcm
    rw [Multiset.map_add]
    norm_num [Multiset.map_cons, Multiset.lcm_cons, Multiset.cons_add]
  have hP : exceptionalPrimes {1 / 2, 1 / 2} {1, 1} = {2} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · rw [mem_exceptionalPrimes, hd]
      norm_num
    · intro p hp
      rw [mem_exceptionalPrimes, hd] at hp
      obtain ⟨hprime, h⟩ := hp
      have h2 := hprime.two_le
      rcases h with hdvd | hle
      · have hle2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
        omega
      · simp at hle
        omega
  have hlam : lambda {1 / 2, 1 / 2} {1, 1} 2 = -2 := by
    norm_num [lambda, Multiset.filter_singleton]
  rw [baseConstant, hP, Finset.prod_singleton, hlam]
  norm_num [Multiset.map_cons, Multiset.prod_cons]

example (α β : Multiset ℚ) : GoodScaling α β 0 := by
  intro n
  cases n with
  | zero => exact ⟨1, by simp⟩
  | succ n => exact ⟨0, by simp⟩

end MetaMathlibExt.HypergeometricNIntegrality
