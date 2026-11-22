/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Zhang--Zagier height
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import MathlibExt.NumberTheory.Height.AbsoluteLogHeightRoots

@[expose] public section

namespace MathlibExt.NumberTheory.Height

/-!
# Zhang--Zagier height

This file defines the Zhang--Zagier height and its essential minimum on the algebraic numbers.
Mathlib's `NumberField.absLogHeight₁` is the source's degree-normalized naïve logarithmic height:
`MathlibExt.NumberTheory.Height.AbsoluteWanted.absLogHeight₁_eq_log_leadingCoeff_add_sum_log_roots`
expresses it using the primitive integral minimal polynomial's leading coefficient and complex
roots, with multiplicity.

Source: teorth/optimizationproblems, “Essential minimum of the Zhang-Zagier height,”
`constants/82a.md`, frozen at commit `2c1968cd520b60f1cf3cf50749f7285e800e4e15`, file
SHA-256 `57cb09c5be0b7ae18221ff1223c40ed55ae915e582c3af8cd9bc34f83bf8799b`.
-/

/-- The Zhang--Zagier height `h(α) + h(1 - α)` of an algebraic number. -/
noncomputable def zhangZagierHeight (α : AlgebraicClosure ℚ) : ℝ :=
  NumberField.absLogHeight₁ α + NumberField.absLogHeight₁ (1 - α)

/-- The Zhang--Zagier height is nonnegative. -/
theorem zhangZagierHeight_nonneg (α : AlgebraicClosure ℚ) :
    0 ≤ zhangZagierHeight α := by
  exact add_nonneg (NumberField.absLogHeight₁_nonneg α)
    (NumberField.absLogHeight₁_nonneg (1 - α))

/-- Algebraic numbers whose Zhang--Zagier height is at most `H`. -/
def zhangZagierSublevelSet (H : ℝ) : Set (AlgebraicClosure ℚ) :=
  {α | zhangZagierHeight α ≤ H}

/-- A real threshold whose Zhang--Zagier sublevel set is finite. -/
def IsZhangZagierFiniteThreshold (H : ℝ) : Prop :=
  (zhangZagierSublevelSet H).Finite

/-- A negative Zhang--Zagier threshold has an empty sublevel set. -/
theorem zhangZagierSublevelSet_eq_empty_of_neg {H : ℝ} (hH : H < 0) :
    zhangZagierSublevelSet H = ∅ := by
  ext α
  simp only [zhangZagierSublevelSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hα
  exact (not_lt_of_ge (zhangZagierHeight_nonneg α)) (lt_of_le_of_lt hα hH)

/-- Every negative real number is a finite Zhang--Zagier threshold. -/
theorem isZhangZagierFiniteThreshold_of_neg {H : ℝ} (hH : H < 0) :
    IsZhangZagierFiniteThreshold H := by
  rw [IsZhangZagierFiniteThreshold, zhangZagierSublevelSet_eq_empty_of_neg hH]
  exact Set.finite_empty

/--
The essential minimum of the Zhang--Zagier height: the supremum of real thresholds whose sublevel
set is finite.
-/
noncomputable def zhangZagierEssentialMinimum : ℝ :=
  sSup {H : ℝ | IsZhangZagierFiniteThreshold H}

/-- The trivial non-strict lower bound recorded in the source. -/
theorem zero_le_zhangZagierEssentialMinimum :
    0 ≤ zhangZagierEssentialMinimum := by
  let S : Set ℝ := {H : ℝ | IsZhangZagierFiniteThreshold H}
  change 0 ≤ sSup S
  by_cases hS : BddAbove S
  · by_contra h
    have hsup : sSup S < 0 := lt_of_not_ge h
    have hhalf_neg : sSup S / 2 < 0 := by linarith
    have hhalf_mem : sSup S / 2 ∈ S :=
      isZhangZagierFiniteThreshold_of_neg hhalf_neg
    have hhalf_le : sSup S / 2 ≤ sSup S := le_csSup hS hhalf_mem
    linarith
  · rw [Real.sSup_of_not_bddAbove hS]

end MathlibExt.NumberTheory.Height
