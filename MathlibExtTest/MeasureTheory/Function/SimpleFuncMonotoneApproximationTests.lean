/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Function.SimpleFuncMonotoneApproximation
public import Mathlib.MeasureTheory.Function.SimpleFunc

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal
open MathlibExt.MeasureTheory.Function.SimpleFuncMonotoneApproximation

namespace MathlibExtTest.MeasureTheory.Function.SimpleFuncMonotoneApproximation

/-- Monotone approximation of the constant function `2`, with the uniform
error `< 1 / 2` on the whole domain (where `f ≤ 2`). -/
example : ∃ φ : ℕ → SimpleFunc ℕ ℝ≥0∞,
    (∀ n a, φ n a ≤ 2) ∧ (Monotone fun n => (φ n : ℕ → ℝ≥0∞)) ∧
    (∀ a, Tendsto (fun n => φ n a) atTop (𝓝 (2 : ℝ≥0∞))) ∧
    ∃ N : ℕ, ∀ n ≥ N, ∀ a, (2 : ℝ≥0∞) - φ n a < 1 / 2 := by
  obtain ⟨φ, ⟨hle, hmono⟩, htendsto, hunif⟩ :=
    exists_monotone_tendsto (f := fun _ : ℕ => (2 : ℝ≥0∞)) measurable_const
  refine ⟨φ, fun n a => hle n a, hmono, fun a => htendsto a, ?_⟩
  obtain ⟨N, hN⟩ := hunif 2 (by norm_num) (1 / 2) (by norm_num)
  exact ⟨N, fun n hn a => hN n hn a le_rfl⟩

/-- Monotone approximation of the unbounded function `n ↦ n`: the uniform
error bound still holds on the bounded set `{a | a ≤ 2}`. -/
example : ∃ φ : ℕ → SimpleFunc ℕ ℝ≥0∞,
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℕ, (a : ℝ≥0∞) ≤ 2 → (a : ℝ≥0∞) - φ n a < 1 / 2 := by
  obtain ⟨φ, ⟨-, -⟩, -, hunif⟩ :=
    exists_monotone_tendsto (f := fun a : ℕ => (a : ℝ≥0∞)) (by measurability)
  obtain ⟨N, hN⟩ := hunif 2 (by norm_num) (1 / 2) (by norm_num)
  exact ⟨φ, N, fun n hn a ha => hN n hn a ha⟩

/-- The uniform bound applied directly to the canonical approximants
`SimpleFunc.eapprox`, without going through the existential witness. -/
example : ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℕ,
    (2 : ℝ≥0∞) - SimpleFunc.eapprox (fun _ : ℕ => (2 : ℝ≥0∞)) n a < 1 / 2 := by
  obtain ⟨N, hN⟩ :=
    eapprox_uniform_on_bounded (f := fun _ : ℕ => (2 : ℝ≥0∞)) measurable_const 2
      (by norm_num) (1 / 2) (by norm_num)
  exact ⟨N, fun n hn a => hN n hn a le_rfl⟩

/-- Monotone approximation of the zero function is identically zero. -/
example : ∃ φ : ℕ → SimpleFunc ℕ ℝ≥0∞, ∀ n a, φ n a = 0 := by
  obtain ⟨φ, ⟨hle, -⟩, -, -⟩ :=
    exists_monotone_tendsto (f := fun _ : ℕ => (0 : ℝ≥0∞)) measurable_const
  exact ⟨φ, fun n a => le_antisymm (hle n a) bot_le⟩

end MathlibExtTest.MeasureTheory.Function.SimpleFuncMonotoneApproximation
