/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Two floor-function identities

The ATLAS wiki article *Two floor-function identities* cites Lemma 6, parts (iii) and (v), of
Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Phakhinkon Napp Phunphayap and
Prapanpong Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic
Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8.
-/

namespace MetaMathlibExt

open Int

/-- The floors of a real number and its negative sum to zero at integers and to minus one
elsewhere. Adding two reals produces a carry in the floor exactly when their fractional
parts sum to at least one.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Phakhinkon Napp Phunphayap and
Prapanpong Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic
Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8, Lemma 6
(`jis-2024-24.4.8-lem-6`). -/
public theorem floor_add_floor_neg_and_floor_add_eq :
    (∀ x : ℝ, (∃ n : ℤ, x = n) → ⌊x⌋ + ⌊-x⌋ = 0) ∧
      (∀ x : ℝ, (¬ ∃ n : ℤ, x = n) → ⌊x⌋ + ⌊-x⌋ = -1) ∧
      ∀ x y : ℝ, ⌊x + y⌋ =
        if fract x + fract y < 1 then ⌊x⌋ + ⌊y⌋ else ⌊x⌋ + ⌊y⌋ + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    simp [floor_neg]
  · intro x hx
    have hx' : x ∉ Set.range (Int.cast : ℤ → ℝ) := fun ⟨n, hn⟩ => hx ⟨n, hn.symm⟩
    rw [floor_neg, (ceil_eq_floor_add_one_iff_notMem x).2 hx']
    omega
  · intro x y
    have hsum : x + y = ((⌊x⌋ + ⌊y⌋ : ℤ) : ℝ) + (fract x + fract y) := by
      rw [Int.cast_add, add_add_add_comm, floor_add_fract, floor_add_fract]
    rw [hsum, floor_intCast_add]
    split_ifs with h
    · rw [floor_eq_zero_iff.mpr ⟨add_nonneg (fract_nonneg x) (fract_nonneg y), h⟩, add_zero]
    · congr 1
      apply floor_eq_iff.mpr
      rw [Int.cast_one]
      exact ⟨le_of_not_gt h, add_lt_add (fract_lt_one x) (fract_lt_one y)⟩

end MetaMathlibExt
