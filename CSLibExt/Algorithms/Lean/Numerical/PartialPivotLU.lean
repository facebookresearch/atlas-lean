/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring

/-!
# Columnwise growth in partial-pivot LU

At each step choose a largest-magnitude entry in the first column of the trailing matrix,
swap its row to the front, and eliminate below it. The pivot rule bounds each multiplier by
one, so each step at most doubles the maximum absolute entry in each remaining column.
The recursive row permutation also permutes the multipliers already computed for that column.

The factorization works in exact arithmetic over a linearly ordered field, including for
singular matrices. A zero maximal pivot means the whole column is zero and requires no update.
The result is the multiplier and columnwise element growth bound from J. W. Demmel, Math 221,
Lecture 5, UC Berkeley, 19 September 2024. No floating-point error claim is made here.
The lower factor's triangularity and diagonal proofs follow the lower-border lemmas in
`MathlibExt/LinearAlgebra/Matrix/GaussPivot.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Numerical.PartialPivotLU

open Matrix Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The first row maximizing the absolute value of the first-column entry. -/
def pivotRow {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) : Fin (n + 1) :=
  ((List.finRange (n + 1)).argmax (fun i => |A i 0|)).getD 0

omit [IsStrictOrderedRing K] in
private theorem abs_le_pivotRow {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (i : Fin (n + 1)) : |A i 0| ≤ |A (pivotRow A) 0| := by
  unfold pivotRow
  generalize h : (List.finRange (n + 1)).argmax (fun i => |A i 0|) = r
  cases r with
  | none =>
      have hn := (List.argmax_eq_none.mp h)
      have hi : i ∈ List.finRange (n + 1) := List.mem_finRange i
      rw [hn] at hi
      cases hi
  | some p =>
      exact List.le_of_mem_argmax (f := fun j : Fin (n + 1) => |A j 0|)
        (List.mem_finRange i) (by rw [h]; simp)

/-- Exchange the first row with the chosen partial pivot row. -/
def pivoted {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  A.submatrix (Equiv.swap 0 (pivotRow A)) id

/-- The multipliers below the pivot. At a zero pivot they are all zero. -/
def multiplier {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (i : Fin n) : K :=
  B i.succ 0 / B 0 0

/-- The trailing matrix after subtracting the multiple of the pivot row from each lower row. -/
def schur {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) K) : Matrix (Fin n) (Fin n) K :=
  fun i j => B i.succ j.succ - multiplier B i * B 0 j.succ

/-- Row permutation and the two factors produced by Gaussian elimination. -/
structure Factors (n : ℕ) (K : Type*) where
  /-- Output row `i` is taken from input row `perm i`. -/
  perm : Equiv.Perm (Fin n)
  /-- Unit lower triangular factor. -/
  lower : Matrix (Fin n) (Fin n) K
  /-- Upper triangular factor. -/
  upper : Matrix (Fin n) (Fin n) K

/-- Gaussian elimination with partial pivoting, written recursively on the trailing matrix. -/
def factor : {n : ℕ} → Matrix (Fin n) (Fin n) K → Factors n K
  | 0, _ => ⟨Equiv.refl _, 1, 0⟩
  | _n + 1, A =>
    let B := pivoted A
    let F := factor (schur B)
    ⟨Equiv.Perm.decomposeFin.symm (pivotRow A, F.perm),
      Matrix.of (Fin.cons (Fin.cons 1 (fun _ => 0))
        (fun i => Fin.cons (multiplier B (F.perm i)) (F.lower i))),
      Matrix.of (Fin.cons (B 0) (fun i => Fin.cons 0 (F.upper i)))⟩

omit [IsStrictOrderedRing K] in
private theorem abs_le_pivoted {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (i : Fin (n + 1)) : |pivoted A i 0| ≤ |pivoted A 0 0| := by
  simpa [pivoted] using abs_le_pivotRow A (Equiv.swap 0 (pivotRow A) i)

private theorem abs_multiplier_le {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (i : Fin n) : |multiplier (pivoted A) i| ≤ 1 := by
  by_cases h : pivoted A 0 0 = 0
  · simp [multiplier, h]
  · rw [multiplier, abs_div, div_le_one₀ (abs_pos.mpr h)]
    exact abs_le_pivoted A i.succ

private theorem multiplier_mul_pivot {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (i : Fin n) : multiplier (pivoted A) i * pivoted A 0 0 = pivoted A i.succ 0 := by
  by_cases h : pivoted A 0 0 = 0
  · have hz := abs_le_pivoted A i.succ
    rw [h, abs_zero, abs_nonpos_iff] at hz
    simp [h, hz]
  · exact div_mul_cancel₀ _ h

/-- **Partial-pivot LU factorization.** The factors are unit lower triangular and upper
triangular, and their product is the row-permuted input. No nonsingularity is assumed. -/
theorem factor_spec {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    let F := factor A
    F.lower.IsLowerTriangular ∧ (∀ i, F.lower i i = 1) ∧ F.upper.IsUpperTriangular ∧
      F.lower * F.upper = A.submatrix F.perm id := by
  induction n with
  | zero =>
      refine ⟨fun {i} => Fin.elim0 i, fun i => Fin.elim0 i, fun {i} => Fin.elim0 i, ?_⟩
      exact Matrix.ext fun i _ => Fin.elim0 i
  | succ n ih =>
      let B := pivoted A
      let F := factor (schur B)
      obtain ⟨hL, hd, hU, hmul⟩ := ih (schur B)
      dsimp only [factor]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => exact (lt_irrefl _ hij).elim
            | succ j => simp
        | succ i =>
            cases j using Fin.cases with
            | zero => exact (Fin.not_lt_zero _ hij).elim
            | succ j => exact hL (Fin.succ_lt_succ_iff.mp hij)
      · intro i
        cases i using Fin.cases with
        | zero => simp
        | succ i => simpa only [Matrix.of_apply, Fin.cons_succ] using hd i
      · intro i j hij
        cases i using Fin.cases with
        | zero => exact (Fin.not_lt_zero _ hij).elim
        | succ i =>
            cases j using Fin.cases with
            | zero => simp
            | succ j => exact hU (Fin.succ_lt_succ_iff.mp hij)
      · ext i j
        rw [Matrix.mul_apply, Fin.sum_univ_succ]
        cases i using Fin.cases with
        | zero => simp [pivoted]
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                simp only [Matrix.of_apply, Fin.cons_succ, Fin.cons_zero, mul_zero,
                  Finset.sum_const_zero, add_zero, Matrix.submatrix_apply,
                  Equiv.Perm.decomposeFin_symm_apply_succ, id_eq]
                exact multiplier_mul_pivot A (F.perm i)
            | succ j =>
                have hij := congrArg (fun X : Matrix (Fin n) (Fin n) K => X i j) hmul
                change (F.lower * F.upper) i j = schur B (F.perm i) j at hij
                rw [Matrix.mul_apply] at hij
                simp only [Matrix.of_apply, Fin.cons_succ, Fin.cons_zero, Matrix.submatrix_apply,
                  Equiv.Perm.decomposeFin_symm_apply_succ, id_eq]
                change multiplier B (F.perm i) * B 0 j.succ +
                  (∑ k, F.lower i k * F.upper k j) = B (F.perm i).succ j.succ
                rw [hij]
                change multiplier B (F.perm i) * B 0 j.succ +
                  (B (F.perm i).succ j.succ - multiplier B (F.perm i) * B 0 j.succ) =
                  B (F.perm i).succ j.succ
                rw [add_sub_cancel]

/-- **Bounded partial-pivot multipliers.** Every entry of the lower factor has modulus at
most one, including after subsequent row exchanges. -/
theorem abs_factor_lower_le_one {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    |(factor A).lower i j| ≤ 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      dsimp only [factor]
      cases i using Fin.cases with
      | zero => cases j using Fin.cases <;> simp
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              simpa only [Matrix.of_apply, Fin.cons_succ, Fin.cons_zero] using
                abs_multiplier_le A ((factor (schur (pivoted A))).perm i)
          | succ j =>
              simpa only [Matrix.of_apply, Fin.cons_succ] using ih (schur (pivoted A)) i j

/-- **Columnwise element growth under partial pivoting.** If `b j` bounds the modulus of
all entries of input column `j`, then the entries of the same column of the upper factor
have modulus at most `2^(n-1) * b j`. -/
private theorem abs_factor_upper_le {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (b : Fin n → K)
    (hb : ∀ i j, |A i j| ≤ b j) (i j : Fin n) :
    |(factor A).upper i j| ≤ (2 : K) ^ (n - 1) * b j := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      let B := pivoted A
      have hB (i j : Fin (n + 1)) : |B i j| ≤ b j :=
        hb (Equiv.swap 0 (pivotRow A) i) j
      have hb₀ (j : Fin (n + 1)) : 0 ≤ b j := (abs_nonneg (B 0 j)).trans (hB 0 j)
      have hpow : (1 : K) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      simp only [factor, Nat.add_sub_cancel]
      cases i using Fin.cases with
      | zero =>
          exact (hB 0 j).trans (le_mul_of_one_le_left (hb₀ j) hpow)
      | succ i =>
          cases j using Fin.cases with
          | zero => simpa using mul_nonneg (pow_nonneg (by norm_num : (0 : K) ≤ 2) n) (hb₀ 0)
          | succ j =>
              have hD (r c : Fin n) : |schur B r c| ≤ 2 * b c.succ := by
                unfold schur
                calc
                  _ ≤ |B r.succ c.succ| + |multiplier B r * B 0 c.succ| := abs_sub _ _
                  _ = |B r.succ c.succ| + |multiplier B r| * |B 0 c.succ| := by rw [abs_mul]
                  _ ≤ b c.succ + 1 * b c.succ := by
                    exact add_le_add (hB _ _) (mul_le_mul (abs_multiplier_le A r)
                      (hB _ _) (abs_nonneg _) zero_le_one)
                  _ = _ := by ring
              have hn : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt
                (Nat.zero_lt_of_lt j.isLt))
              simpa only [Matrix.of_apply, Fin.cons_succ, ← mul_assoc, ← pow_succ, hn] using
                ih (schur B) (fun c => 2 * b c.succ) hD i j

/-- **Maximum absolute entry of a nonempty column of the upper factor.** The upper factor from
partial-pivot LU grows by at most `2^n` in each column of an `(n+1)`-square matrix. -/
theorem columnMax_factor_upper_le {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (j : Fin (n + 1)) :
    univ.sup' univ_nonempty (fun i => |(factor A).upper i j|) ≤
      (2 : K) ^ n * univ.sup' univ_nonempty (fun i => |A i j|) := by
  refine sup'_le _ _ fun i _ => ?_
  simpa only [Nat.add_sub_cancel] using abs_factor_upper_le A
    (fun c => univ.sup' univ_nonempty (fun r => |A r c|))
    (fun r c => le_sup' (fun t => |A t c|) (mem_univ r)) i j

end Cslib.Algorithms.Lean.Numerical.PartialPivotLU
