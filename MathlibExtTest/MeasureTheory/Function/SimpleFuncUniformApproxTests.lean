/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Function.SimpleFuncUniformApprox

/-!
# Tests for simple-function approximation

* For the constant function `1`, the approximating simple functions stay
  below `1`, are monotone, and converge to `1` pointwise.
* The uniform part: for the constant function `1` with bound `B = 2` and
  `ε = 1 / 2`, some `N` works for every `n ≥ N` and every point.
* The `ε = ⊤` branch of the uniform lemma, for the constant function `1`.
* The `B = 0` case: for the zero function, the uniform bound holds with
  error `< 1`.
* The bundled statement for the constant function `2`, with its uniform
  part giving error `< 1 / 2` on the whole domain.
* Monotone approximation of the unbounded function `n ↦ n`: the uniform
  error bound still holds on the bounded set `{a | a ≤ 2}`.
* Monotone approximation of the zero function is identically zero.
-/

open MathlibExt.MeasureTheory.Function.SimpleFuncUniformApprox
open MeasureTheory Filter Topology
open scoped ENNReal

namespace MathlibExtTest.MeasureTheory.Function.SimpleFuncUniformApproxTests

/-- The approximating sequence for the constant function `1` is below `1`,
monotone, and converges pointwise to `1`. -/
example :
    ∃ φ : ℕ → SimpleFunc ℝ ℝ≥0∞,
      ((∀ n a, φ n a ≤ 1) ∧ (Monotone fun n => (φ n : ℝ → ℝ≥0∞))) ∧
      (∀ a, Tendsto (fun n => φ n a) atTop (𝓝 (1 : ℝ≥0∞))) := by
  obtain ⟨φ, ⟨hle, hmono⟩, htendsto, -⟩ :=
    exists_monotone_tendsto (f := fun _ : ℝ => (1 : ℝ≥0∞)) measurable_const
  exact ⟨φ, ⟨hle, hmono⟩, htendsto⟩

/-- Uniform approximation of the constant function `1` on `{f ≤ 2}` with `ε = 1 / 2`. -/
example :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℝ, (1 : ℝ≥0∞) ≤ 2 →
      (1 : ℝ≥0∞) - SimpleFunc.eapprox (fun _ : ℝ => (1 : ℝ≥0∞)) n a < 1 / 2 :=
  eapprox_sub_lt_of_le (f := fun _ : ℝ => (1 : ℝ≥0∞)) measurable_const
    (B := 2) (ε := 1 / 2) (by norm_num) (by norm_num)

/-- The `ε = ⊤` branch: the uniform lemma still yields an `N` for `ε = ⊤`. -/
example :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℝ, (1 : ℝ≥0∞) ≤ 1 →
      (1 : ℝ≥0∞) - SimpleFunc.eapprox (fun _ : ℝ => (1 : ℝ≥0∞)) n a < ⊤ :=
  eapprox_sub_lt_of_le (f := fun _ : ℝ => (1 : ℝ≥0∞)) measurable_const
    (B := 1) (ε := (⊤ : ℝ≥0∞)) (by norm_num) (by simp)

/-- The `B = 0` case: the zero function is approximated with error `< 1`. -/
example :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℝ, (0 : ℝ≥0∞) ≤ 0 →
      (0 : ℝ≥0∞) - SimpleFunc.eapprox (fun _ : ℝ => (0 : ℝ≥0∞)) n a < 1 :=
  eapprox_sub_lt_of_le (f := fun _ : ℝ => (0 : ℝ≥0∞)) measurable_const
    (B := 0) (ε := 1) (by norm_num) (by norm_num)

/-- Monotone approximation of the constant function `2`, with the uniform
error `< 1 / 2` on the whole domain (where `f ≤ 2`): the bundled statement with its
uniform part, through the existential witness. -/
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

/-- Monotone approximation of the zero function is identically zero. -/
example : ∃ φ : ℕ → SimpleFunc ℕ ℝ≥0∞, ∀ n a, φ n a = 0 := by
  obtain ⟨φ, ⟨hle, -⟩, -, -⟩ :=
    exists_monotone_tendsto (f := fun _ : ℕ => (0 : ℝ≥0∞)) measurable_const
  exact ⟨φ, fun n a => le_antisymm (hle n a) bot_le⟩

end MathlibExtTest.MeasureTheory.Function.SimpleFuncUniformApproxTests
