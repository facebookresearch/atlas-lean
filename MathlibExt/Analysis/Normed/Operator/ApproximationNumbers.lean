/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Linarith

/-!
# Approximation numbers for native continuous linear operators

The approximation number at index `n` is the infimum of `‖T-R‖` over
continuous linear operators whose range has cardinal rank at most `n`.
No finite-dimensional assumption on either carrier is made.

The indexing begins with `a₀(T)=‖T‖`. Classical approximation numbers
defined using rank strictly less than a positive index `k` correspond to
this definition at `k-1`.

This supplies the infinite-dimensional continuous-linear-map surface left
as a TODO in Mathlib's finite-dimensional singular-values API. Cardinal
rank is used because `finrank` alone is zero for infinite-dimensional
ranges and cannot express the finite-rank constraint.
-/

@[expose] public section

noncomputable section

universe u v

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- Operator-norm errors of all approximants with actual cardinal range rank at most `n`. -/
def approximationErrorSet (T : E →L[𝕜] F) (n : ℕ) : Set ℝ :=
  {r | ∃ R : E →L[𝕜] F, R.toLinearMap.rank ≤ (n : Cardinal) ∧ r = ‖T - R‖}

/-- Membership records the actual finite-rank operator and its operator-norm error. -/
@[simp] theorem mem_approximationErrorSet (T : E →L[𝕜] F) (n : ℕ) (r : ℝ) :
    r ∈ approximationErrorSet T n ↔
      ∃ R : E →L[𝕜] F, R.toLinearMap.rank ≤ (n : Cardinal) ∧ r = ‖T - R‖ := Iff.rfl

/-- The zero approximant always gives the original operator norm as an admissible error. -/
theorem norm_mem_approximationErrorSet (T : E →L[𝕜] F) (n : ℕ) :
    ‖T‖ ∈ approximationErrorSet T n := by
  refine ⟨0, ?_, by simp⟩
  simp

/-- Finite-rank approximation errors form a nonempty set. -/
theorem approximationErrorSet_nonempty (T : E →L[𝕜] F) (n : ℕ) :
    (approximationErrorSet T n).Nonempty :=
  ⟨‖T‖, norm_mem_approximationErrorSet T n⟩

/-- Every actual approximation error is nonnegative. -/
theorem approximationErrorSet_nonneg (T : E →L[𝕜] F) (n : ℕ)
    {r : ℝ} (h : r ∈ approximationErrorSet T n) : 0 ≤ r := by
  obtain ⟨R, _, rfl⟩ := h
  exact norm_nonneg _

/-- The error set is bounded below by zero before taking the real infimum. -/
theorem approximationErrorSet_bddBelow (T : E →L[𝕜] F) (n : ℕ) :
    BddBelow (approximationErrorSet T n) :=
  ⟨0, fun _ h => approximationErrorSet_nonneg T n h⟩

/-- The approximation number at index `n`, using rank at most `n` and the real operator norm. -/
def approximationNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ :=
  sInf (approximationErrorSet T n)

/-- Approximation numbers are nonnegative. -/
theorem approximationNumber_nonneg (T : E →L[𝕜] F) (n : ℕ) :
    0 ≤ approximationNumber T n :=
  le_csInf (approximationErrorSet_nonempty T n) (fun _ h => approximationErrorSet_nonneg T n h)

/-- The zero approximant bounds every approximation number by the operator norm. -/
theorem approximationNumber_le_norm (T : E →L[𝕜] F) (n : ℕ) :
    approximationNumber T n ≤ ‖T‖ :=
  csInf_le (approximationErrorSet_bddBelow T n) (norm_mem_approximationErrorSet T n)

/-- Any admissible finite-rank operator bounds the approximation number by its actual error. -/
theorem approximationNumber_le_norm_sub (T : E →L[𝕜] F) (n : ℕ)
    (R : E →L[𝕜] F) (hR : R.toLinearMap.rank ≤ (n : Cardinal)) :
    approximationNumber T n ≤ ‖T - R‖ :=
  csInf_le (approximationErrorSet_bddBelow T n) ⟨R, hR, rfl⟩

/-- Enlarging the permitted rank enlarges the set of admissible errors. -/
theorem approximationErrorSet_mono (T : E →L[𝕜] F) {n m : ℕ} (h : n ≤ m) :
    approximationErrorSet T n ⊆ approximationErrorSet T m := by
  rintro r ⟨R, hR, hr⟩
  exact ⟨R, hR.trans (Nat.cast_le.mpr h), hr⟩

/-- Approximation numbers decrease when more finite-rank approximants are allowed. -/
theorem approximationNumber_antitone (T : E →L[𝕜] F) : Antitone (approximationNumber T) := by
  intro n m h
  apply le_csInf (approximationErrorSet_nonempty T n)
  intro r hr
  exact csInf_le (approximationErrorSet_bddBelow T m) (approximationErrorSet_mono T h hr)

/-- Cardinal range rank zero forces the actual operator to be zero. -/
private theorem eq_zero_of_rank_le_zero (R : E →L[𝕜] F)
    (hR : R.toLinearMap.rank ≤ (0 : Cardinal)) : R = 0 := by
  have hbot : LinearMap.range R.toLinearMap = ⊥ :=
    Submodule.rank_eq_zero.mp (le_antisymm hR (zero_le : (0 : Cardinal) ≤ R.toLinearMap.rank))
  have hlinear : R.toLinearMap = 0 := LinearMap.range_eq_bot.mp hbot
  ext x
  simpa using LinearMap.congr_fun hlinear x

/-- Index zero permits only the zero operator, so its approximation number is the operator norm. -/
@[simp] theorem approximationNumber_zero_index (T : E →L[𝕜] F) :
    approximationNumber T 0 = ‖T‖ := by
  apply le_antisymm (approximationNumber_le_norm T 0)
  apply le_csInf (approximationErrorSet_nonempty T 0)
  rintro r ⟨R, hR, rfl⟩
  rw [eq_zero_of_rank_le_zero R hR, sub_zero]

/-- An operator with cardinal range rank at most `n` has zero approximation error at that index. -/
theorem approximationNumber_eq_zero_of_rank_le (T : E →L[𝕜] F) (n : ℕ)
    (hT : T.toLinearMap.rank ≤ (n : Cardinal)) : approximationNumber T n = 0 := by
  apply le_antisymm _ (approximationNumber_nonneg T n)
  simpa using approximationNumber_le_norm_sub T n T hT

/-- Every approximation number of the zero operator is zero. -/
@[simp] theorem approximationNumber_zero (n : ℕ) :
    approximationNumber (0 : E →L[𝕜] F) n = 0 := by
  apply approximationNumber_eq_zero_of_rank_le
  simp

/-- A common finite-rank approximant gives the one-sided operator-norm stability inequality. -/
theorem approximationNumber_le_add_norm_sub (T S : E →L[𝕜] F) (n : ℕ) :
    approximationNumber T n ≤ approximationNumber S n + ‖T - S‖ := by
  have h : approximationNumber T n - ‖T - S‖ ≤ approximationNumber S n := by
    apply le_csInf (approximationErrorSet_nonempty S n)
    rintro r ⟨R, hR, rfl⟩
    have h₁ := approximationNumber_le_norm_sub T n R hR
    have h₂ := dist_triangle T S R
    simp only [dist_eq_norm] at h₂
    linarith
  linarith

/-- Approximation numbers are 1-Lipschitz in the native operator norm. -/
theorem abs_approximationNumber_sub_le_norm (T S : E →L[𝕜] F) (n : ℕ) :
    |approximationNumber T n - approximationNumber S n| ≤ ‖T - S‖ := by
  have h₁ := approximationNumber_le_add_norm_sub T S n
  have h₂ := approximationNumber_le_add_norm_sub S T n
  rw [norm_sub_rev S T] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end ContinuousLinearMap
