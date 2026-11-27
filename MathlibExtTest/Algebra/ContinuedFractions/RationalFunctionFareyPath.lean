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

/- The signed continuants `(-1) ^ i * B_i` of `[0; X, X, X, X]`, with the numerators
`(-1) ^ i * A_i`, form a path whose adjacent determinants alternate as `(-1) ^ i`. -/
private noncomputable def altDen : ℕ → ℚ[X]
  | 0 => 1
  | 1 => -X
  | 2 => X ^ 2 + 1
  | 3 => -(X ^ 3 + 2 * X)
  | 4 => X ^ 4 + 3 * X ^ 2 + 1
  | _ => 0

private noncomputable def altNum : ℕ → ℚ[X]
  | 0 => 0
  | 1 => -1
  | 2 => X
  | 3 => -(X ^ 2 + 1)
  | 4 => X ^ 3 + 2 * X
  | _ => 0

private noncomputable def altQuot : ℕ → ℚ[X]
  | 0 => 0
  | _ + 1 => X

-- Along this path every partial quotient is `X`, and the signs `(-1) ^ i` cancel: the theorem
-- recovers the continuants of `[0; X, X, X, X]`.
example : (∀ i, 1 ≤ i → i ≤ 4 → 0 < (altQuot i).natDegree) ∧
    (polyContFract altQuot 4).nums 1 = algebraMap ℚ[X] (RatFunc ℚ) 1 ∧
    (polyContFract altQuot 4).dens 1 = algebraMap ℚ[X] (RatFunc ℚ) X ∧
    (polyContFract altQuot 4).nums 3 = algebraMap ℚ[X] (RatFunc ℚ) (X ^ 2 + 1) ∧
    (polyContFract altQuot 4).dens 3 = algebraMap ℚ[X] (RatFunc ℚ) (X ^ 3 + 2 * X) ∧
    (polyContFract altQuot 4).nums 4 = algebraMap ℚ[X] (RatFunc ℚ) (X ^ 3 + 2 * X) ∧
    (polyContFract altQuot 4).dens 4 = algebraMap ℚ[X] (RatFunc ℚ) (X ^ 4 + 3 * X ^ 2 + 1) := by
  have hdegree (i : ℕ) (hi : i ≤ 4) : (altDen i).degree = i := by
    interval_cases i <;> norm_num [altDen] <;> compute_degree!
  have hdeg : ∀ i, 1 ≤ i → i ≤ 4 → (altDen (i - 1)).degree < (altDen i).degree := by
    intro i hi hin
    rw [hdegree (i - 1) (by omega), hdegree i hin]
    exact_mod_cast (show i - 1 < i by omega)
  have hdet : ∀ i, 1 ≤ i → i ≤ 4 →
      altNum i * altDen (i - 1) - altNum (i - 1) * altDen i = C ((-1) ^ i) := by
    intro i hi hin
    interval_cases i <;> norm_num [altNum, altDen] <;> ring
  have ha : ∀ i, 2 ≤ i → i ≤ 4 → altQuot i = C ((-1) ^ i) *
      (altNum i * altDen (i - 2) - altNum (i - 2) * altDen i) := by
    intro i hi hin
    interval_cases i <;> norm_num [altQuot, altNum, altDen] <;> ring
  obtain ⟨hpos, hconv⟩ := polyContFract_of_farey_path_det_neg_one_pow altNum altDen 4 rfl hdeg
    hdet altQuot rfl (by norm_num [altQuot, altDen]) ha
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(hconv 1 (by decide)).1]
    congr 1
    norm_num [altNum]
  · rw [(hconv 1 (by decide)).2]
    congr 1
    norm_num [altDen]
  · rw [(hconv 3 (by decide)).1]
    congr 1
    norm_num [altNum]
  · rw [(hconv 3 (by decide)).2]
    congr 1
    norm_num [altDen]
  · rw [(hconv 4 le_rfl).1]
    congr 1
    norm_num [altNum]
  · rw [(hconv 4 le_rfl).2]
    congr 1
    norm_num [altDen]

end MathlibExtTest.RationalFunctionFareyPath
