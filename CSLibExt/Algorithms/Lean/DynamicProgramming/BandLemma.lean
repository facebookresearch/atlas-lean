/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.BandedAlignment

/-!
# The band lemma for banded alignment

Ukkonen's band observation (Ukkonen 1985, used for the `O(k · min(m, n))` banded edit-distance
algorithm): when every column costs something nonnegative and a gap column costs at least one,
an alignment of cost at most `k` never leaves the diagonal band `|i - j| ≤ k`. Each gap column
moves the alignment path one diagonal off and costs at least one, while a match or substitution
column keeps the diagonal. In the score convention of `nwScore` (maximization, scores are
negated costs) the hypotheses are `σ a b ≤ 0` and `gap ≤ -1`.

This discharges the hypothesis of `bandedScore_eq_nwScore_of_banded_optimal`: if the optimal
score is at least `-k`, every optimal alignment is `k`-banded, so the banded optimum with band
width `k` equals the unrestricted Needleman–Wunsch optimum. Unit-cost Levenshtein distance is
the case `σ a b = if a = b then 0 else -1`, `gap = -1`.

## Main results

* `bandedFrom_of_abs_add_gapColumns_le`: the offset difference along any prefix is bounded by
  the starting difference plus the number of gap columns.
* `alignmentScore_le_neg_gapColumns`: with `σ ≤ 0` and `gap ≤ -1` the score is at most minus
  the number of gap columns.
* `isBanded_of_neg_le_alignmentScore`: **the band lemma**: an alignment scoring at least `-k`
  is `k`-banded.
* `bandedScore_eq_nwScore_of_neg_le`: the banded optimum with width `k` is exact whenever the
  optimum is at least `-k`.

Not covered: the `O(ND)` running-time analysis; `bandedScore` remains the banded
specification of `BandedAlignment` rather than a tabulated banded table. The furthest-reaching
(wavefront) recurrence for linear gap costs is in `WavefrontAlignment`.

## References

* E. Ukkonen, *Algorithms for approximate string matching*, Information and Control 64 (1985),
  100–118.
* G. Navarro, *A guided tour to approximate string matching*, ACM Comput. Surv. 33 (2001),
  31–88.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

variable {α : Type u}

/-- The number of gap columns of an alignment: columns with exactly one letter. -/
def gapColumns : Alignment α → ℕ
  | [] => 0
  | (some _, some _) :: A => gapColumns A
  | (some _, none) :: A => gapColumns A + 1
  | (none, some _) :: A => gapColumns A + 1
  | (none, none) :: A => gapColumns A

/-- Along every prefix, the offset difference is at most the starting difference plus the number
of gap columns: an alignment starting at `(i, j)` stays in the band of width `w` as soon as
`|i - j| + gapColumns A ≤ w`. -/
theorem bandedFrom_of_abs_add_gapColumns_le (w : ℕ) :
    ∀ (A : Alignment α) (i j : ℕ),
      |(i : ℤ) - (j : ℤ)| + (gapColumns A : ℤ) ≤ (w : ℤ) → bandedFrom w i j A = true
  | [], i, j, h => by
      simp only [gapColumns, Nat.cast_zero, add_zero] at h
      simpa [bandedFrom] using h
  | (some _, some _) :: A, i, j, h => by
      simp only [gapColumns] at h
      simp only [bandedFrom, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨by have := (gapColumns A).cast_nonneg (α := ℤ); linarith, ?_⟩
      apply bandedFrom_of_abs_add_gapColumns_le w A (i + 1) (j + 1)
      have : ((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) = (i : ℤ) - (j : ℤ) := by push_cast; ring
      rw [this]
      exact h
  | (some _, none) :: A, i, j, h => by
      simp only [gapColumns, Nat.cast_add, Nat.cast_one] at h
      simp only [bandedFrom, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨by have := (gapColumns A).cast_nonneg (α := ℤ); linarith, ?_⟩
      apply bandedFrom_of_abs_add_gapColumns_le w A (i + 1) j
      have hcast : ((i + 1 : ℕ) : ℤ) - (j : ℤ) = ((i : ℤ) - (j : ℤ)) + 1 := by push_cast; ring
      rw [hcast]
      have := abs_add_le ((i : ℤ) - (j : ℤ)) 1
      rw [show |(1 : ℤ)| = 1 by decide] at this
      linarith
  | (none, some _) :: A, i, j, h => by
      simp only [gapColumns, Nat.cast_add, Nat.cast_one] at h
      simp only [bandedFrom, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨by have := (gapColumns A).cast_nonneg (α := ℤ); linarith, ?_⟩
      apply bandedFrom_of_abs_add_gapColumns_le w A i (j + 1)
      have hcast : (i : ℤ) - ((j + 1 : ℕ) : ℤ) = ((i : ℤ) - (j : ℤ)) + (-1) := by push_cast; ring
      rw [hcast]
      have := abs_add_le ((i : ℤ) - (j : ℤ)) (-1)
      rw [show |(-1 : ℤ)| = 1 by decide] at this
      linarith
  | (none, none) :: A, i, j, h => by
      simp only [gapColumns] at h
      simp only [bandedFrom, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨by have := (gapColumns A).cast_nonneg (α := ℤ); linarith, ?_⟩
      exact bandedFrom_of_abs_add_gapColumns_le w A i j h

/-- An alignment with at most `w` gap columns is `w`-banded. -/
theorem isBanded_of_gapColumns_le {w : ℕ} {A : Alignment α} (h : gapColumns A ≤ w) :
    IsBanded w A :=
  bandedFrom_of_abs_add_gapColumns_le w A 0 0 (by simpa using h)

/-- With nonpositive substitution scores and gap score at most `-1`, an alignment scores at most
minus its number of gap columns. -/
theorem alignmentScore_le_neg_gapColumns {σ : α → α → ℤ} {gap : ℤ}
    (hσ : ∀ a b, σ a b ≤ 0) (hgap : gap ≤ -1) :
    ∀ A : Alignment α, alignmentScore σ gap A ≤ -(gapColumns A : ℤ)
  | [] => by simp [alignmentScore, gapColumns]
  | (some a, some b) :: A => by
      have ih := alignmentScore_le_neg_gapColumns hσ hgap A
      have := hσ a b
      simp only [alignmentScore, List.map_cons, List.sum_cons, columnScore, gapColumns] at ih ⊢
      linarith
  | (some _, none) :: A => by
      have ih := alignmentScore_le_neg_gapColumns hσ hgap A
      simp only [alignmentScore, List.map_cons, List.sum_cons, columnScore, gapColumns,
        Nat.cast_add, Nat.cast_one] at ih ⊢
      linarith
  | (none, some _) :: A => by
      have ih := alignmentScore_le_neg_gapColumns hσ hgap A
      simp only [alignmentScore, List.map_cons, List.sum_cons, columnScore, gapColumns,
        Nat.cast_add, Nat.cast_one] at ih ⊢
      linarith
  | (none, none) :: A => by
      have ih := alignmentScore_le_neg_gapColumns hσ hgap A
      simp only [alignmentScore, List.map_cons, List.sum_cons, columnScore, gapColumns] at ih ⊢
      linarith

/-- **The band lemma** (Ukkonen 1985): with nonpositive substitution scores and gap score at
most `-1`, every alignment scoring at least `-w` (cost at most `w`) is `w`-banded. -/
theorem isBanded_of_neg_le_alignmentScore {σ : α → α → ℤ} {gap : ℤ}
    (hσ : ∀ a b, σ a b ≤ 0) (hgap : gap ≤ -1) {w : ℕ} {A : Alignment α}
    (h : -(w : ℤ) ≤ alignmentScore σ gap A) : IsBanded w A := by
  apply isBanded_of_gapColumns_le
  have := alignmentScore_le_neg_gapColumns hσ hgap A
  exact_mod_cast (show (gapColumns A : ℤ) ≤ w by linarith)

/-- **The banded optimum is exact** when the optimal score is at least `-w` (optimal cost at
most `w`), for nonpositive substitution scores and gap score at most `-1`: some optimal
alignment exists and, by the band lemma, it is `w`-banded. -/
theorem bandedScore_eq_nwScore_of_neg_le {σ : α → α → ℤ} {gap : ℤ}
    (hσ : ∀ a b, σ a b ≤ 0) (hgap : gap ≤ -1) {w : ℕ} {xs ys : List α}
    (h : -(w : ℤ) ≤ nwScore σ gap xs ys) :
    bandedScore σ gap w xs ys = some (nwScore σ gap xs ys) := by
  obtain ⟨A, hA, hscore⟩ := exists_alignmentScore_eq_nwScore σ gap xs ys
  exact bandedScore_eq_nwScore_of_banded_optimal σ gap w
    ⟨A, hA, isBanded_of_neg_le_alignmentScore hσ hgap (hscore ▸ h), hscore⟩

end Cslib.Algorithms.Lean
