/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Matrix.Basic

/-!
# Pairing power sums by diagonal matrix traces

## References

* Peiran Ding, Yanjun Zhu and Lei Wang, *A New Formula for the Sum of Integer Powers Based on
  Elementary Matrix Theory*, INTEGERS 25 (2025), Article A98, pp. 1–15, Lemma 1 (§2.3, p. 4).
  <https://math.colgate.edu/~integers/z98/z98.pdf>
-/

namespace MathlibExt.LinearAlgebra.PowerSumMatrixWanted

open Finset

/-- **Lemma 1**: for a positive integer `k` and an even
positive integer `n = 2s`,
`1^k + ⋯ + n^k = ∑_{i=1}^s Tr (M_i^k)` with
`M_i = diag(i, 2s + 1 - i)`. Stated for all `n, k ∈ ℕ`
with `n` even (it also holds at `k = 0` and `n = 0`).

Source: Peiran Ding, Yanjun Zhu and Lei Wang, "A New
Formula for the Sum of Integer Powers Based on
Elementary Matrix Theory", INTEGERS 25 (2025), Article A98, Lemma 1 (`integers-2025-A98-lem-1`). -/
public theorem sum_pow_eq_sum_trace_of_even (n k : ℕ)
    (hn : Even n) :
    ∑ i ∈ Finset.Icc 1 n, (i : ℝ) ^ k =
      ∑ i ∈ Finset.Icc 1 (n / 2),
        Matrix.trace
          (Matrix.diagonal ![(i : ℝ), 2 * (n / 2 : ℕ) + 1 - i] ^ k) := by
  obtain ⟨s, hs⟩ := hn
  have hn : n = 2 * s := by omega
  rw [hn, show 2 * s / 2 = s by omega]
  have hsplit : Icc 1 (2 * s) = Icc 1 s ∪ Icc (s + 1) (2 * s) := by
    ext i
    simp only [mem_union, mem_Icc]
    omega
  have hdisj : Disjoint (Icc 1 s) (Icc (s + 1) (2 * s)) := by
    rw [Finset.disjoint_left]
    simp only [mem_Icc]
    omega
  have hreflect : ∑ i ∈ Icc (s + 1) (2 * s), (i : ℝ) ^ k =
      ∑ i ∈ Icc 1 s, (((2 * s + 1 - i : ℕ) : ℝ) ^ k) := by
    refine sum_bij (fun i _ ↦ 2 * s + 1 - i) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [mem_Icc] at hi ⊢
      omega
    · intro i hi j hj hij
      simp only [mem_Icc] at hi hj
      omega
    · intro i hi
      simp only [mem_Icc] at hi ⊢
      exact ⟨2 * s + 1 - i, by omega, by omega⟩
    · intro i hi
      have h : 2 * s + 1 - (2 * s + 1 - i) = i := by
        rw [mem_Icc] at hi
        omega
      rw [h]
  rw [hsplit, sum_union hdisj, hreflect, ← sum_add_distrib]
  refine sum_congr rfl fun i hi ↦ ?_
  have hle : i ≤ 2 * s + 1 := by
    rw [mem_Icc] at hi
    omega
  simp only [Matrix.diagonal_pow, Matrix.trace_diagonal, Fin.sum_univ_two, Pi.pow_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]

end MathlibExt.LinearAlgebra.PowerSumMatrixWanted
