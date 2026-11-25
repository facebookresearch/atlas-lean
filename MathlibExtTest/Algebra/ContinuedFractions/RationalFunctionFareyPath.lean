/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.ContinuedFractions.RationalFunctionFareyPath
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

namespace MathlibExtTest.RationalFunctionFareyPath

open MetaMathlibExt Polynomial

-- A length-zero continued fraction has its head and no partial terms.
example (a : ℕ → ℚ[X]) :
    (polyContFract a 0).h = algebraMap ℚ[X] (RatFunc ℚ) (a 0) ∧
      ∀ i, (polyContFract a 0).s.get? i = none := by
  simp [polyContFract_h, polyContFract_s_get?]

private noncomputable def sampleDen : ℕ → ℚ[X]
  | 0 => 1
  | 1 => X
  | 2 => X ^ 2 - 1
  | 3 => X ^ 3 - 2 * X
  | 4 => X ^ 4 - 3 * X ^ 2 + 1
  | _ => 0

private noncomputable def sampleNum : ℕ → ℚ[X]
  | 0 => 0
  | i + 1 => sampleDen i

private noncomputable def sampleQuot : ℕ → ℚ[X]
  | 0 => 0
  | i + 1 => C ((-1) ^ (i + 2)) * X

-- The path reaches both negative signs and returns to a positive sign at index four.
example : (∀ i, 1 ≤ i → i ≤ 4 → 0 < (sampleQuot i).natDegree) ∧
    (polyContFract sampleQuot 4).dens 1 = algebraMap ℚ[X] (RatFunc ℚ) X ∧
    (polyContFract sampleQuot 4).nums 2 = algebraMap ℚ[X] (RatFunc ℚ) (-X) ∧
    (polyContFract sampleQuot 4).dens 3 = algebraMap ℚ[X] (RatFunc ℚ) (-(X ^ 3 - 2 * X)) ∧
    (polyContFract sampleQuot 4).nums 4 = algebraMap ℚ[X] (RatFunc ℚ) (X ^ 3 - 2 * X) ∧
    (polyContFract sampleQuot 4).dens 4 = algebraMap ℚ[X] (RatFunc ℚ) (X ^ 4 - 3 * X ^ 2 + 1) := by
  have hdegree (i : ℕ) (hi : i ≤ 4) : (sampleDen i).degree = i := by
    interval_cases i <;> norm_num [sampleDen] <;> compute_degree!
  have hdeg : ∀ i, 1 ≤ i → i ≤ 4 → (sampleDen (i - 1)).degree < (sampleDen i).degree := by
    intro i hi hin
    rw [hdegree (i - 1) (by omega), hdegree i hin]
    exact_mod_cast (show i - 1 < i by omega)
  have hdet : ∀ i, 1 ≤ i → i ≤ 4 →
      sampleNum i * sampleDen (i - 1) - sampleNum (i - 1) * sampleDen i = 1 := by
    intro i hi hin
    interval_cases i <;> norm_num [sampleNum, sampleDen] <;> ring
  have ha : ∀ i, 2 ≤ i → i ≤ 4 → sampleQuot i = C ((-1) ^ (i + 1)) *
      (sampleNum i * sampleDen (i - 2) - sampleNum (i - 2) * sampleDen i) := by
    intro i hi hin
    interval_cases i <;> norm_num [sampleQuot, sampleNum, sampleDen] <;> ring
  obtain ⟨hpos, hconv⟩ := polyContFract_of_farey_path_det_one sampleNum sampleDen 4 rfl hdeg hdet
    sampleQuot rfl (by norm_num [sampleQuot, sampleDen]) ha
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [sampleDen] using (hconv 1 (by decide)).2
  · simpa [sampleNum, sampleDen] using (hconv 2 (by decide)).1
  · simpa [sampleDen] using (hconv 3 (by decide)).2
  · simpa [sampleNum, sampleDen] using (hconv 4 (by decide)).1
  · simpa [sampleDen] using (hconv 4 le_rfl).2

end MathlibExtTest.RationalFunctionFareyPath
