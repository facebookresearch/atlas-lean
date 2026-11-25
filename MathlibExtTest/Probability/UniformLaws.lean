/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.UniformLaws
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Probability.UniformLaws` -/

namespace MathlibExtTest.UniformLaws

open MeasureTheory MathlibExt.Probability.UniformLawsWanted

variable {𝓧 : Type*} [MeasurableSpace 𝓧] (P : Measure 𝓧) [IsProbabilityMeasure P]

-- Test section: the definitions. For the empty class both quantities are `0`, the value of an
-- empty supremum of reals.
example (F : Empty → 𝓧 → ℝ) {n : ℕ} (hn : 1 ≤ n) (x : Fin n → 𝓧) :
    uniformDeviation P F hn x = 0 ∧ rademacherComplexity P F hn = 0 := by
  simp [uniformDeviation, rademacherComplexity]

-- A constant function has no deviation: its empirical mean is its expectation.
example (a : ℝ) {n : ℕ} (hn : 1 ≤ n) (x : Fin n → 𝓧) :
    uniformDeviation P (fun (_ : Unit) (_ : 𝓧) => a) hn x = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp [uniformDeviation, field]

-- For one sample point the two sign vectors give the same absolute value, so the Rademacher
-- complexity is the expected supremum of `|F i (X)|`.
theorem rademacherComplexity_one {ι : Type*} (F : ι → 𝓧 → ℝ) :
    rademacherComplexity P F le_rfl =
      ∫ x, ⨆ i, |F i (x 0)| ∂(Measure.pi fun _ : Fin 1 => P) := by
  unfold rademacherComplexity
  congr 1 with x
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  simp
  ring

-- Test section: symmetrization. With one sample point it reads
-- `E[sup_i |F i (X) - E[F i]|] ≤ 2 E[sup_i |F i (X)|]`.
example {ι : Type*} [Countable ι] (F : ι → 𝓧 → ℝ) (hF : ∀ i, Measurable (F i)) {b : ℝ}
    (hb : ∀ i y, |F i y| ≤ b) :
    ∫ x, ⨆ i, |F i (x 0) - ∫ y, F i y ∂P| ∂(Measure.pi fun _ : Fin 1 => P) ≤
      2 * ∫ x, ⨆ i, |F i (x 0)| ∂(Measure.pi fun _ : Fin 1 => P) := by
  have h := integral_uniformDeviation_le_two_mul_rademacherComplexity P F hF hb le_rfl
  simpa [uniformDeviation, rademacherComplexity_one] using h

-- Test section: bounded differences. Changing one of `n` sample points moves the uniform deviation
-- of a class of `[-1, 1]`-valued functions by at most `2 / n`.
example {ι : Type*} (F : ι → 𝓧 → ℝ) (hb : ∀ i y, |F i y| ≤ 1) {n : ℕ} (hn : 1 ≤ n)
    (x : Fin n → 𝓧) (k : Fin n) (y : 𝓧) :
    |uniformDeviation P F hn (Function.update x k y) - uniformDeviation P F hn x| ≤ 2 / n := by
  simpa using abs_uniformDeviation_update_sub_le zero_le_one hb hn x k y

-- Test section: the uniform law. For a class of `[-1, 1]`-valued functions, the uniform deviation
-- is at most `2 R_n(F) + δ` with probability at least `1 - exp (-n δ² / 2)`.
example {ι : Type*} [Countable ι] (F : ι → 𝓧 → ℝ) (hF : ∀ i, Measurable (F i))
    (hb : ∀ i y, |F i y| ≤ 1) {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 ≤ δ) :
    1 - Real.exp (-(n : ℝ) * δ ^ 2 / 2) ≤
      (Measure.pi fun _ : Fin n => P).real
        {x | uniformDeviation P F hn x ≤ 2 * rademacherComplexity P F hn + δ} := by
  simpa using uniformDeviation_le_two_mul_rademacherComplexity_add P F hF one_pos hb hn hδ

-- The concentration step: with probability at least `1 - exp (-n δ² / (2 b²))` the uniform
-- deviation is within `δ` above its mean; for `δ = 0` the bound is `0` and says nothing.
example {ι : Type*} [Countable ι] (F : ι → 𝓧 → ℝ) (hF : ∀ i, Measurable (F i)) {b : ℝ}
    (hb0 : 0 < b) (hb : ∀ i y, |F i y| ≤ b) {n : ℕ} (hn : 1 ≤ n) :
    1 - Real.exp (-(n : ℝ) * 0 ^ 2 / (2 * b ^ 2)) = 0 ∧
      1 - Real.exp (-(n : ℝ) * 0 ^ 2 / (2 * b ^ 2)) ≤
        (Measure.pi fun _ : Fin n => P).real
          {x | uniformDeviation P F hn x ≤
            ∫ x', uniformDeviation P F hn x' ∂(Measure.pi fun _ : Fin n => P) + 0} :=
  ⟨by simp, uniformDeviation_le_integral_uniformDeviation_add hF hb0 hb hn le_rfl⟩

-- The uniform deviation is measurable, so the event above is measurable.
example {ι : Type*} [Countable ι] (F : ι → 𝓧 → ℝ) (hF : ∀ i, Measurable (F i)) {n : ℕ}
    (hn : 1 ≤ n) (t : ℝ) : MeasurableSet {x : Fin n → 𝓧 | uniformDeviation P F hn x ≤ t} :=
  measurableSet_le (measurable_uniformDeviation hF hn) measurable_const

end MathlibExtTest.UniformLaws
