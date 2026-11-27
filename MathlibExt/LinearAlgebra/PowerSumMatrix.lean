/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Traces of powers of a two-by-two matrix

The Girard–Waring formula expresses the trace of a matrix power in terms of the trace and
determinant of the original matrix.
-/

namespace MathlibExt.LinearAlgebra.PowerSumMatrixWanted

open Finset

private theorem trace_pow_step (M : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) :
    (M ^ (n + 2)).trace = M.trace * (M ^ (n + 1)).trace + (-M.det) * (M ^ n).trace := by
  have h : M ^ 2 - M.trace • M + M.det • (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
    simpa [Matrix.charpoly_fin_two, map_add, map_sub, map_mul, map_pow,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mul] using Matrix.aeval_self_charpoly M
  have h₂ : M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    calc
      _ = (M ^ 2 - M.trace • M + M.det • 1) + (M.trace • M - M.det • 1) := by abel
      _ = _ := by rw [h, zero_add]
  rw [show M ^ (n + 2) = M ^ 2 * M ^ n by rw [← pow_add, Nat.add_comm 2 n],
    h₂, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, one_mul, ← pow_succ',
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, neg_mul, sub_eq_add_neg]
  simp only [smul_eq_mul]

-- Summands of the sequence with initial values `1` and `t`, using `d` for the
-- signed determinant. Their support is `2 * r ≤ n`.
private noncomputable def term (t d : ℝ) (n r : ℕ) : ℝ :=
  ((n - r).choose r : ℝ) * d ^ r * t ^ (n - 2 * r)

private theorem term_zero (t d : ℝ) (n : ℕ) : term t d n 0 = t ^ n := by
  simp [term]

private theorem term_eq_zero (t d : ℝ) {n r : ℕ} (h : n < 2 * r) : term t d n r = 0 := by
  have hc : n - r < r := by omega
  simp [term, Nat.choose_eq_zero_of_lt hc]

private theorem term_step (t d : ℝ) (n r : ℕ) :
    term t d (n + 2) (r + 1) = t * term t d (n + 1) (r + 1) + d * term t d n r := by
  by_cases h : 2 * r ≤ n
  · have hp : (n + 2 - (r + 1)).choose (r + 1) =
        (n - r).choose r + (n + 1 - (r + 1)).choose (r + 1) := by
      rw [show n + 2 - (r + 1) = (n - r) + 1 by omega,
        show n + 1 - (r + 1) = n - r by omega, Nat.choose_succ_succ']
    by_cases htop : n = 2 * r
    · -- At the even endpoint, the contribution from degree `n + 1` vanishes.
      have hz := term_eq_zero t d (n := n + 1) (r := r + 1) (by omega)
      rw [hz, mul_zero, zero_add]
      have hc : (n + 1 - (r + 1)).choose (r + 1) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      rw [hc, add_zero] at hp
      unfold term
      rw [hp, show n + 2 - 2 * (r + 1) = n - 2 * r by omega, pow_succ d r]
      ring
    · unfold term
      rw [hp, Nat.cast_add, show n + 2 - 2 * (r + 1) = n - 2 * r by omega,
        show n - 2 * r = (n + 1 - 2 * (r + 1)) + 1 by omega,
        pow_succ t, pow_succ d r]
      ring
  · rw [term_eq_zero t d (n := n + 2) (r := r + 1) (by omega),
      term_eq_zero t d (n := n + 1) (r := r + 1) (by omega), term_eq_zero t d (n := n) (by omega)]
    simp

private noncomputable def binomialSum (t d : ℝ) (n : ℕ) : ℝ :=
  ∑ r ∈ range (n / 2 + 1), term t d n r

private theorem binomialSum_eq_range (t d : ℝ) (n b : ℕ) (hb : n / 2 + 1 ≤ b) :
    binomialSum t d n = ∑ r ∈ range b, term t d n r := by
  apply sum_subset (range_mono hb)
  intro r _ hr
  exact term_eq_zero t d (by simp only [mem_range, not_lt] at hr; omega)

private theorem binomialSum_step (t d : ℝ) (n : ℕ) :
    binomialSum t d (n + 2) = t * binomialSum t d (n + 1) + d * binomialSum t d n := by
  let b := n / 2 + 1
  rw [binomialSum_eq_range t d (n + 2) (b + 1) (by dsimp [b]; omega),
    binomialSum_eq_range t d (n + 1) (b + 1) (by dsimp [b]; omega)]
  change _ = _ + d * ∑ r ∈ range b, term t d n r
  rw [sum_range_succ' (f := term t d (n + 2)), sum_range_succ' (f := term t d (n + 1))]
  simp only [term_zero, mul_add, mul_sum, pow_succ' t (n + 1)]
  rw [add_right_comm, ← sum_add_distrib]
  simp only [← term_step]

-- Adding the shifted binomial sum changes the initial values from `1, t` to `2, t`.
private theorem trace_pow_eq_binomialSum (M : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) :
    (M ^ (n + 2)).trace = binomialSum M.trace (-M.det) (n + 2) +
      (-M.det) * binomialSum M.trace (-M.det) n := by
  have hs₀ : (1 : Matrix (Fin 2) (Fin 2) ℝ).trace = 2 := by simp [Matrix.trace_one]
  have h₀ : binomialSum M.trace (-M.det) 0 = 1 := by simp [binomialSum, term_zero]
  have h₁ : binomialSum M.trace (-M.det) 1 = M.trace := by simp [binomialSum, term_zero]
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [trace_pow_step M 0, binomialSum_step _ _ 0, h₀, h₁, pow_zero, pow_one, hs₀]
    ring
  | one =>
    rw [trace_pow_step M 1, trace_pow_step M 0, binomialSum_step _ _ 1,
      binomialSum_step _ _ 0, h₀, h₁, pow_zero, pow_one, hs₀]
    ring
  | more n ih₀ ih₁ =>
    rw [trace_pow_step M (n + 2), ih₁, ih₀, binomialSum_step _ _ (n + 2),
      binomialSum_step _ _ n]
    ring

private theorem factorial_cast_ne_zero (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero n

private theorem choose_cast_eq (n r : ℕ) (h : r ≤ n) :
    (n.choose r : ℝ) = (n.factorial : ℝ) / ((r.factorial : ℝ) * ((n - r).factorial : ℝ)) := by
  apply (eq_div_iff (mul_ne_zero (factorial_cast_ne_zero _) (factorial_cast_ne_zero _))).2
  rw [← mul_assoc]
  exact_mod_cast Nat.choose_mul_factorial_mul_factorial h

private theorem factorial_cast_eq {n : ℕ} (h : 0 < n) :
    (n.factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  simp [Nat.factorial_succ]

private theorem factorial_coeff_zero {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * (((k - 1).factorial : ℝ) / (k.factorial : ℝ)) = 1 := by
  rw [← mul_div_assoc, ← factorial_cast_eq hk, div_self (factorial_cast_ne_zero _)]

private theorem factorial_coeff_succ {k r : ℕ} (h : 2 * (r + 1) ≤ k) :
    (k : ℝ) * ((k - (r + 1) - 1).factorial : ℝ) /
        (((r + 1).factorial : ℝ) * ((k - 2 * (r + 1)).factorial : ℝ)) =
      ((k - (r + 1)).choose (r + 1) : ℝ) + ((k - (r + 1) - 1).choose r : ℝ) := by
  rw [choose_cast_eq _ _ (by omega), choose_cast_eq _ _ (by omega),
    show k - (r + 1) - (r + 1) = k - 2 * (r + 1) by omega,
    show k - (r + 1) - 1 - r = k - 2 * (r + 1) by omega,
    factorial_cast_eq (show 0 < k - (r + 1) by omega),
    factorial_cast_eq (show 0 < r + 1 by omega), Nat.add_sub_cancel,
    Nat.cast_sub (by omega : r + 1 ≤ k)]
  have hr : ((r + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  field_simp [factorial_cast_ne_zero, hr]
  ring

private theorem trace_pow_factorial (M : Matrix (Fin 2) (Fin 2) ℝ) (k : ℕ) (hk : 2 ≤ k) :
    (M ^ k).trace = (k : ℝ) * ∑ r ∈ range (k / 2 + 1),
      (-1 : ℝ) ^ r *
        (((k - r - 1).factorial : ℝ) / ((r.factorial : ℝ) * ((k - 2 * r).factorial : ℝ))) *
        M.det ^ r * M.trace ^ (k - 2 * r) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  let b := n / 2 + 1
  rw [trace_pow_eq_binomialSum]
  unfold binomialSum
  rw [show (n + 2) / 2 + 1 = b + 1 by dsimp [b]; omega,
    sum_range_succ' (f := term M.trace (-M.det) (n + 2))]
  conv_rhs => rw [sum_range_succ', mul_add]
  simp only [mul_sum]
  rw [add_right_comm, ← sum_add_distrib]
  refine congrArg₂ (· + ·) (sum_congr rfl fun r hr ↦ ?_) ?_
  · have hb : 2 * (r + 1) ≤ n + 2 := by rw [mem_range] at hr; dsimp [b] at hr; omega
    have hcoeff := factorial_coeff_succ hb
    unfold term
    rw [show n - r = n + 2 - (r + 1) - 1 by omega,
      show n - 2 * r = n + 2 - 2 * (r + 1) by omega]
    calc
      _ = (((n + 2 - (r + 1)).choose (r + 1) : ℝ) + ((n + 2 - (r + 1) - 1).choose r : ℝ)) *
          (-M.det) ^ (r + 1) * M.trace ^ (n + 2 - 2 * (r + 1)) := by
        rw [pow_succ (-M.det) r]
        ring
      _ = _ := by
        rw [← hcoeff, ← neg_one_mul M.det, mul_pow]
        ring
  · simp only [term_zero, pow_zero, one_mul, Nat.sub_zero, Nat.mul_zero,
      Nat.factorial_zero, Nat.cast_one, mul_one]
    rw [← mul_assoc, factorial_coeff_zero (by omega), one_mul]

/-- **Traces of powers of a $2 \times 2$ matrix.** Let $M$ be a real $2 \times 2$ matrix and
let $m \ge 1$ be an integer. Then
$$\operatorname{tr}(M^{2m}) = 2m \sum_{r=0}^{m} (-1)^r \frac{(2m - r - 1)!}{r! \, (2m - 2r)!}
(\det M)^r (\operatorname{tr} M)^{2m - 2r}$$
and
$$\operatorname{tr}(M^{2m+1}) = (2m + 1) \sum_{r=0}^{m} (-1)^r
\frac{(2m - r)!}{r! \, (2m + 1 - 2r)!} (\det M)^r (\operatorname{tr} M)^{2m + 1 - 2r}.$$

Source: Peiran Ding, Yanjun Zhu and Lei Wang, "A New
Formula for the Sum of Integer Powers Based on
Elementary Matrix Theory", Theorem 1, equations (5)
and (6). -/
public theorem trace_pow_two (M : Matrix (Fin 2) (Fin 2) ℝ)
    (m : ℕ) (hm : 1 ≤ m) :
    Matrix.trace (M ^ (2 * m)) =
        (2 * m : ℝ) * ∑ r ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ r *
            ((Nat.factorial (2 * m - r - 1) : ℝ) /
              ((Nat.factorial r : ℝ) *
                (Nat.factorial (2 * m - 2 * r) : ℝ))) *
            M.det ^ r * Matrix.trace M ^ (2 * m - 2 * r) ∧
      Matrix.trace (M ^ (2 * m + 1)) =
        (2 * m + 1 : ℝ) * ∑ r ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ r *
            ((Nat.factorial (2 * m - r) : ℝ) /
              ((Nat.factorial r : ℝ) *
                (Nat.factorial (2 * m + 1 - 2 * r) : ℝ))) *
            M.det ^ r * Matrix.trace M ^ (2 * m + 1 - 2 * r) := by
  constructor
  · simpa only [Nat.cast_mul, Nat.cast_ofNat, show 2 * m / 2 = m by omega] using
      trace_pow_factorial M (2 * m) (by omega)
  · have h := trace_pow_factorial M (2 * m + 1) (by omega)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      show (2 * m + 1) / 2 = m by omega] at h
    refine h.trans (congrArg (_ * ·) (sum_congr rfl fun r _ ↦ ?_))
    rw [show 2 * m + 1 - r - 1 = 2 * m - r by omega]

end MathlibExt.LinearAlgebra.PowerSumMatrixWanted
