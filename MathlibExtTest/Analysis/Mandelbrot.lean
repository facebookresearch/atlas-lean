/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Mandelbrot
import Mathlib.Tactic.NormNum

/-!
# Tests for Mandelbrot connectedness

The parameter `-2` has a critical orbit that lands on the fixed point `2`.
At parameter `1` the orbit grows at least linearly.
-/

open MathlibExt.Analysis.MandelbrotWanted.ComplexAnalysis.MandelbrotProblem

example : ConnectedSpace Mandelbrot := isConnected_iff_connectedSpace.mp mandelbrot_connected

example : (-2 : ℂ) ∈ Mandelbrot := by
  have h₂ : (Tc (-2))^[2] 0 = 2 := by norm_num [Function.iterate_succ_apply', Tc]
  have hfix : Tc (-2) 2 = 2 := by norm_num [Tc]
  refine ⟨2, fun n => ?_⟩
  match n with
  | 0 => norm_num
  | 1 => norm_num [Tc]
  | k + 2 =>
    rw [Function.iterate_add_apply, h₂, Function.iterate_fixed hfix]
    norm_num

example : (1 : ℂ) ∉ Mandelbrot := by
  have hg (n : ℕ) : ∃ k : ℕ, n ≤ k ∧ (Tc 1)^[n] 0 = (k : ℂ) := by
    induction n with
    | zero => exact ⟨0, le_rfl, by simp⟩
    | succ n ih =>
      obtain ⟨k, hk, hv⟩ := ih
      refine ⟨k ^ 2 + 1, Nat.succ_le_succ (hk.trans (Nat.le_self_pow (by decide) k)), ?_⟩
      rw [Function.iterate_succ_apply', hv]
      simp [Tc]
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := exists_nat_gt M
  obtain ⟨k, hk, he⟩ := hg n
  have h := hM n
  rw [he] at h
  have hbound : (k : ℝ) ≤ M := by simpa using h
  exact (hn.trans_le (Nat.cast_le.mpr hk)).not_ge hbound
