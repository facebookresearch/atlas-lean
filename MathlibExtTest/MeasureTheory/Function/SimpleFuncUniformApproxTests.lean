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

end MathlibExtTest.MeasureTheory.Function.SimpleFuncUniformApproxTests
