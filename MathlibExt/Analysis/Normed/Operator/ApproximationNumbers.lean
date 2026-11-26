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
# Finite-rank approximation numbers of bounded operators

For normed spaces over a nontrivially normed field, define `a_n(T)=inf {‖T-R‖ : dim(range R)≤n}`
for bounded linear approximants `R`. Cardinal range dimension gives the finite-rank constraint
even when the ambient spaces are infinite-dimensional.

This indexing starts at `a_0(T)=‖T‖`. The numbers are nonnegative, nonincreasing in `n`, at most
`‖T‖`, and satisfy `|a_n(T)-a_n(S)|≤‖T-S‖`. Rank at most `n` implies `a_n(T)=0`. Completeness of
the spaces and existence of an optimal approximant are not assumed.
-/

@[expose] public section

noncomputable section

universe u v

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- **Errors of rank-bounded operator approximants.** Let `𝕜` be a nontrivially normed field
and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set `a_n(T)=inf
{‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n : ℕ`.
`approximationErrorSet T n` is `{‖T-R‖ : dim_𝕜(range R)≤n}`, with the operator norm and
bounded linear `R`. -/
def approximationErrorSet (T : E →L[𝕜] F) (n : ℕ) : Set ℝ :=
  {r | ∃ R : E →L[𝕜] F, R.toLinearMap.rank ≤ (n : Cardinal) ∧ r = ‖T - R‖}

/-- **Witness for a finite-rank approximation error.** Let `𝕜` be a nontrivially normed field
and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set `a_n(T)=inf
{‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n : ℕ`. a real
`r` belongs to `approximationErrorSet T n` exactly when there is bounded `R` with cardinal
range dimension at most `n` and `r=‖T-R‖`. -/
@[simp] theorem mem_approximationErrorSet (T : E →L[𝕜] F) (n : ℕ) (r : ℝ) :
    r ∈ approximationErrorSet T n ↔
      ∃ R : E →L[𝕜] F, R.toLinearMap.rank ≤ (n : Cardinal) ∧ r = ‖T - R‖ := Iff.rfl

/-- **Zero approximant gives the operator norm error.** Let `𝕜` be a nontrivially normed field
and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set `a_n(T)=inf
{‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n : ℕ`. for
every `n`, `‖T‖∈approximationErrorSet T n`, witnessed by `R=0`. -/
theorem norm_mem_approximationErrorSet (T : E →L[𝕜] F) (n : ℕ) :
    ‖T‖ ∈ approximationErrorSet T n := by
  refine ⟨0, ?_, by simp⟩
  simp

/-- **Nonempty set of finite-rank errors.** Let `𝕜` be a nontrivially normed field and `E,F`
normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set `a_n(T)=inf {‖T-R‖ : R :
E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n : ℕ`. for every `n`,
`approximationErrorSet T n` is nonempty, containing `‖T‖`. -/
theorem approximationErrorSet_nonempty (T : E →L[𝕜] F) (n : ℕ) :
    (approximationErrorSet T n).Nonempty :=
  ⟨‖T‖, norm_mem_approximationErrorSet T n⟩

/-- **Nonnegativity of every approximation error.** Let `𝕜` be a nontrivially normed field and
`E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set `a_n(T)=inf {‖T-R‖
: R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n : ℕ`. if
`r∈approximationErrorSet T n`, then `0≤r`. -/
theorem approximationErrorSet_nonneg (T : E →L[𝕜] F) (n : ℕ)
    {r : ℝ} (h : r ∈ approximationErrorSet T n) : 0 ≤ r := by
  obtain ⟨R, _, rfl⟩ := h
  exact norm_nonneg _

/-- **Lower bound for the approximation error infimum.** Let `𝕜` be a nontrivially normed
field and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set
`a_n(T)=inf {‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n :
ℕ`. the set `approximationErrorSet T n` is bounded below by zero. -/
theorem approximationErrorSet_bddBelow (T : E →L[𝕜] F) (n : ℕ) :
    BddBelow (approximationErrorSet T n) :=
  ⟨0, fun _ h => approximationErrorSet_nonneg T n h⟩

/-- **Rank-at-most approximation number.** Let `𝕜` be a nontrivially normed field and `E,F`
normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set `a_n(T)=inf {‖T-R‖ : R :
E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n : ℕ`. `approximationNumber
T n=a_n(T)` is the real infimum of rank-at-most-`n` approximation errors. Classical
positive indexing by rank less than `k` corresponds to `n=k-1`. -/
def approximationNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ :=
  sInf (approximationErrorSet T n)

/-- **Nonnegative finite-rank approximation number.** Let `𝕜` be a nontrivially normed field
and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set `a_n(T)=inf
{‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n : ℕ`.
`0≤a_n(T)` for every `n`. -/
theorem approximationNumber_nonneg (T : E →L[𝕜] F) (n : ℕ) :
    0 ≤ approximationNumber T n :=
  le_csInf (approximationErrorSet_nonempty T n) (fun _ h => approximationErrorSet_nonneg T n h)

/-- **Operator norm upper bound for approximation numbers.** Let `𝕜` be a nontrivially normed
field and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set
`a_n(T)=inf {‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n :
ℕ`. `a_n(T)≤‖T‖` for every `n`. -/
theorem approximationNumber_le_norm (T : E →L[𝕜] F) (n : ℕ) :
    approximationNumber T n ≤ ‖T‖ :=
  csInf_le (approximationErrorSet_bddBelow T n) (norm_mem_approximationErrorSet T n)

/-- **Approximation number bounded by an admissible error.** Let `𝕜` be a nontrivially normed
field and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set
`a_n(T)=inf {‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n :
ℕ`. if a bounded `R : E → F` has cardinal range dimension at most `n`, then
`a_n(T)≤‖T-R‖`. -/
theorem approximationNumber_le_norm_sub (T : E →L[𝕜] F) (n : ℕ)
    (R : E →L[𝕜] F) (hR : R.toLinearMap.rank ≤ (n : Cardinal)) :
    approximationNumber T n ≤ ‖T - R‖ :=
  csInf_le (approximationErrorSet_bddBelow T n) ⟨R, hR, rfl⟩

/-- **Larger rank allowance enlarges the error set.** Let `𝕜` be a nontrivially normed field
and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set `a_n(T)=inf
{‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n : ℕ`. if
`n≤m`, `approximationErrorSet T n ⊆ approximationErrorSet T m`. -/
theorem approximationErrorSet_mono (T : E →L[𝕜] F) {n m : ℕ} (h : n ≤ m) :
    approximationErrorSet T n ⊆ approximationErrorSet T m := by
  rintro r ⟨R, hR, hr⟩
  exact ⟨R, hR.trans (Nat.cast_le.mpr h), hr⟩

/-- **Approximation numbers decrease with the allowed rank.** Let `𝕜` be a nontrivially normed
field and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set
`a_n(T)=inf {‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n :
ℕ`. the function `n ↦ a_n(T)` is antitone: `n≤m` implies `a_m(T)≤a_n(T)`. -/
theorem approximationNumber_antitone (T : E →L[𝕜] F) : Antitone (approximationNumber T) := by
  intro n m h
  apply le_csInf (approximationErrorSet_nonempty T n)
  intro r hr
  exact csInf_le (approximationErrorSet_bddBelow T m) (approximationErrorSet_mono T h hr)

/-- **A zero-dimensional operator range forces the zero map.** Let `𝕜` be a nontrivially
normed field and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set
`a_n(T)=inf {‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n :
ℕ`. if bounded `R : E → F` has cardinal range dimension at most zero, then `R=0`. -/
private theorem eq_zero_of_rank_le_zero (R : E →L[𝕜] F)
    (hR : R.toLinearMap.rank ≤ (0 : Cardinal)) : R = 0 := by
  have hbot : LinearMap.range R.toLinearMap = ⊥ :=
    Submodule.rank_eq_zero.mp (le_antisymm hR (zero_le : (0 : Cardinal) ≤ R.toLinearMap.rank))
  have hlinear : R.toLinearMap = 0 := LinearMap.range_eq_bot.mp hbot
  ext x
  simpa using LinearMap.congr_fun hlinear x

/-- **Approximation index zero equals the operator norm.** Let `𝕜` be a nontrivially normed
field and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set
`a_n(T)=inf {‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n :
ℕ`. `a_0(T)=‖T‖`, because the only rank-zero approximant is the zero map. -/
@[simp] theorem approximationNumber_zero_index (T : E →L[𝕜] F) :
    approximationNumber T 0 = ‖T‖ := by
  apply le_antisymm (approximationNumber_le_norm T 0)
  apply le_csInf (approximationErrorSet_nonempty T 0)
  rintro r ⟨R, hR, rfl⟩
  rw [eq_zero_of_rank_le_zero R hR, sub_zero]

/-- **Vanishing approximation number for a rank-bounded operator.** Let `𝕜` be a nontrivially
normed field and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set
`a_n(T)=inf {‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n :
ℕ`. if `dim_𝕜(range T)≤n` as a cardinal inequality, then `a_n(T)=0`. -/
theorem approximationNumber_eq_zero_of_rank_le (T : E →L[𝕜] F) (n : ℕ)
    (hT : T.toLinearMap.rank ≤ (n : Cardinal)) : approximationNumber T n = 0 := by
  apply le_antisymm _ (approximationNumber_nonneg T n)
  simpa using approximationNumber_le_norm_sub T n T hT

/-- **Approximation numbers of the zero operator.** Let `𝕜` be a nontrivially normed field and
`E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set `a_n(T)=inf {‖T-R‖
: R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n : ℕ`. `a_n(0)=0` for
every `n : ℕ`. -/
@[simp] theorem approximationNumber_zero (n : ℕ) :
    approximationNumber (0 : E →L[𝕜] F) n = 0 := by
  apply approximationNumber_eq_zero_of_rank_le
  simp

/-- **One-sided stability of an approximation number.** Let `𝕜` be a nontrivially normed field
and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set `a_n(T)=inf
{‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n : ℕ`. for
bounded `S : E → F`, `a_n(T)≤a_n(S)+‖T-S‖`. -/
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

/-- **Lipschitz bound for finite-rank approximation numbers.** Let `𝕜` be a nontrivially
normed field and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set
`a_n(T)=inf {‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n :
ℕ`. for bounded `S : E → F`, `|a_n(T)-a_n(S)|≤‖T-S‖`. -/
theorem abs_approximationNumber_sub_le_norm (T S : E →L[𝕜] F) (n : ℕ) :
    |approximationNumber T n - approximationNumber S n| ≤ ‖T - S‖ := by
  have h₁ := approximationNumber_le_add_norm_sub T S n
  have h₂ := approximationNumber_le_add_norm_sub S T n
  rw [norm_sub_rev S T] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end ContinuousLinearMap
