/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ScottishBook8
import Mathlib.Tactic.Push

/-! # Tests for Mazur's factorization problem -/

open Filter MathlibExt.Analysis.ScottishBook8Wanted
open scoped Topology

-- Extract the convergent counterexample and an index of failure for each proposed pair.
example : ∃ (z : ℕ → ℝ) (L : ℝ), Tendsto z atTop (𝓝 L) ∧
    ∀ (x y : ℕ → ℝ) (a b : ℝ), Tendsto x atTop (𝓝 a) → Tendsto y atTop (𝓝 b) →
      ∃ n, z n ≠ (∑ k ∈ Finset.range (n + 1), x k * y (n - k)) / (n + 1 : ℝ) := by
  have h := mazur8CauchyProduct_refuted
  unfold ScottishBookProblem8Claim at h
  push Not at h
  obtain ⟨z, ⟨L, hL⟩, hz⟩ := h
  exact ⟨z, L, hL, fun x y a b ha hb => hz x y ⟨a, ha⟩ ⟨b, hb⟩⟩

-- Constant sequences do admit the factorization, including at index zero.
example (c : ℝ) : ∃ (x y : ℕ → ℝ), Tendsto x atTop (𝓝 c) ∧ Tendsto y atTop (𝓝 1) ∧
    ∀ n : ℕ, c = (∑ k ∈ Finset.range (n + 1), x k * y (n - k)) / (n + 1 : ℝ) := by
  refine ⟨fun _ => c, fun _ => 1, tendsto_const_nhds, tendsto_const_nhds, fun n => ?_⟩
  simp [mul_div_cancel_left₀, Nat.cast_add_one_ne_zero]
