/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FatouJulia
import MathlibExt.Analysis.Mandelbrot
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Analysis.FatouJulia` -/

namespace MathlibExtTest.FatouJulia

open MathlibExt.Analysis.FatouJuliaWanted.ComplexAnalysis.FatouJuliaProblem

-- Test section: the definitions.

-- `T_c` is the quadratic map `z ↦ z ^ 2 + c`.
example : Tc 1 2 = 5 := by norm_num [Tc]

-- The Mandelbrot set is the set of parameters whose critical point `0` lies in the filled
-- Julia set.
example (c : ℂ) : c ∈ Mandelbrot ↔ (0 : ℂ) ∈ FilledJulia c := Iff.rfl

open MathlibExt.Analysis.MandelbrotWanted.ComplexAnalysis in
example (c : ℂ) : c ∈ Mandelbrot ↔ c ∈ MandelbrotProblem.Mandelbrot := Iff.rfl

-- For `z ↦ z ^ 2`, the point `1` has a constant orbit and lies in the filled Julia set.
example : (1 : ℂ) ∈ FilledJulia 0 :=
  ⟨1, fun n => by simp [Function.iterate_fixed (show Tc 0 1 = 1 by simp [Tc])]⟩

-- For `z ↦ z ^ 2`, the orbit `2, 4, 16, 256, …` of `2` is unbounded.
private lemma two_notMem_filledJulia_zero : (2 : ℂ) ∉ FilledJulia 0 := by
  have key : ∀ n : ℕ, (n : ℝ) + 2 ≤ ‖(Tc 0)^[n] 2‖ := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      simp only [Tc, add_zero, norm_pow]
      push_cast
      nlinarith
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := exists_nat_gt M
  linarith [key n, hM n]

example : (2 : ℂ) ∉ FilledJulia 0 := two_notMem_filledJulia_zero

-- Test section: the dichotomy.

-- `c = 0`: the orbit of `0` is constant, so `K_0` (the closed unit disc) is connected.
private lemma zero_mem_mandelbrot : (0 : ℂ) ∈ Mandelbrot :=
  ⟨0, fun n => by simp [Function.iterate_fixed (show Tc 0 0 = 0 by simp [Tc])]⟩

example : IsConnected (FilledJulia 0) := (julia_cantor_dichotomy 0).1 zero_mem_mandelbrot

-- `c = -2`, the tip of the Mandelbrot set: the orbit of `0` is `0, -2, 2, 2, …`.
private lemma neg_two_mem_mandelbrot : (-2 : ℂ) ∈ Mandelbrot := by
  have h2 : Tc (-2) 2 = 2 := by norm_num [Tc]
  refine ⟨2, fun n => ?_⟩
  match n with
  | 0 => simp
  | 1 => norm_num [Tc]
  | n + 2 =>
    have h02 : (Tc (-2))^[2] 0 = 2 := by norm_num [Tc]
    rw [Function.iterate_add_apply, h02, Function.iterate_fixed h2]
    norm_num

example : IsConnected (FilledJulia (-2)) :=
  (julia_cantor_dichotomy (-2)).1 neg_two_mem_mandelbrot

-- `c = 1`: the orbit `0, 1, 2, 5, 26, …` of `0` escapes, so `K_1` is a Cantor set.
private lemma one_notMem_mandelbrot : (1 : ℂ) ∉ Mandelbrot := by
  have key : ∀ n : ℕ, ∃ r : ℝ, (Tc 1)^[n] 0 = r ∧ (n : ℝ) ≤ r := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp, by norm_num⟩
    | succ n ih =>
      obtain ⟨r, hr, hnr⟩ := ih
      refine ⟨r ^ 2 + 1, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', hr]
        simp [Tc]
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · norm_num
          positivity
        · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          push_cast
          nlinarith
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := exists_nat_gt M
  obtain ⟨r, hr, hnr⟩ := key n
  have h := hM n
  rw [hr, Complex.norm_real, Real.norm_eq_abs] at h
  linarith [le_abs_self r]

example : Nonempty (FilledJulia 1 ≃ₜ (ℕ → Bool)) :=
  (julia_cantor_dichotomy 1).2 one_notMem_mandelbrot

-- Every parameter falls under one of the two halves.
example (c : ℂ) :
    IsConnected (FilledJulia c) ∨ Nonempty ((FilledJulia c) ≃ₜ (ℕ → Bool)) := by
  by_cases hc : c ∈ Mandelbrot
  · exact Or.inl ((julia_cantor_dichotomy c).1 hc)
  · exact Or.inr ((julia_cantor_dichotomy c).2 hc)

end MathlibExtTest.FatouJulia
