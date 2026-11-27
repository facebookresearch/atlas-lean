/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Traces for sums of powers with an odd endpoint

After setting aside the last power, pair the remaining indices by reflection.
Each pair contributes the trace of a power of a diagonal matrix.

## References

* Peiran Ding, Yanjun Zhu and Lei Wang, *A New Formula for the Sum of Integer Powers Based on
  Elementary Matrix Theory*, INTEGERS 25 (2025), Article A98, pp. 1–15, §2.3, Lemma 2
  (pp. 4–5), using the pairing from Lemma 1 (p. 4).
-/

namespace MathlibExt.LinearAlgebra.PowerSumMatrixWanted

open Finset

/-- **Lemma 2**: for a positive integer `k` and an odd
positive integer `n = 2s + 1`,
`1^k + ⋯ + n^k = ∑_{i=1}^s Tr (M_i^k) + n^k`, with the
matrices `M_i = diag(i, 2s + 1 - i)` of the paper's proof
(the statement leaves `M_i` unspecified). Stated for all
`k ∈ ℕ` (it also holds at `k = 0`).

Source: Peiran Ding, Yanjun Zhu and Lei Wang, "A New
Formula for the Sum of Integer Powers Based on
Elementary Matrix Theory", INTEGERS 25 (2025), Article A98, Lemma 2 (`integers-2025-A98-lem-2`). -/
public theorem sum_pow_eq_sum_trace_add_of_odd (n k : ℕ)
    (hn : Odd n) :
    ∑ i ∈ Finset.Icc 1 n, (i : ℝ) ^ k =
      ∑ i ∈ Finset.Icc 1 (n / 2),
          Matrix.trace
            (Matrix.diagonal ![(i : ℝ), 2 * (n / 2 : ℕ) + 1 - i] ^ k) +
        (n : ℝ) ^ k := by
  let s := n / 2
  have hn' : n = 2 * s + 1 := by
    have h := Nat.odd_iff.mp hn
    dsimp [s]
    omega
  change ∑ i ∈ Icc 1 n, (i : ℝ) ^ k =
    ∑ i ∈ Icc 1 s, Matrix.trace (Matrix.diagonal ![(i : ℝ), 2 * (s : ℝ) + 1 - i] ^ k) +
      (n : ℝ) ^ k
  have hend : Icc 1 n = insert n (Icc 1 (2 * s)) := by
    ext i
    simp only [mem_Icc, mem_insert]
    omega
  have hnot : n ∉ Icc 1 (2 * s) := by simp only [mem_Icc]; omega
  rw [hend, sum_insert hnot, add_comm ((n : ℝ) ^ k)]
  congr 1
  have hsplit : Icc 1 (2 * s) = Icc 1 s ∪ Icc (s + 1) (2 * s) := by
    ext i
    simp only [mem_union, mem_Icc]
    omega
  have hdisj : Disjoint (Icc 1 s) (Icc (s + 1) (2 * s)) := by
    rw [disjoint_left]
    simp only [mem_Icc]
    omega
  -- Reflection sends the lower half bijectively onto the upper half.
  have hreflect : (∑ i ∈ Icc 1 s, ((2 * s + 1 - i : ℕ) : ℝ) ^ k) =
      ∑ i ∈ Icc (s + 1) (2 * s), (i : ℝ) ^ k := by
    refine sum_bij (fun i _ ↦ 2 * s + 1 - i) ?_ ?_ ?_ (fun _ _ ↦ rfl)
    · intro i hi
      simp only [mem_Icc] at hi ⊢
      omega
    · intro i hi j hj hij
      simp only [mem_Icc] at hi hj
      omega
    · intro j hj
      simp only [mem_Icc] at hj
      exact ⟨2 * s + 1 - j, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  rw [hsplit, sum_union hdisj, ← hreflect, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ 2 * s + 1 := by have := (mem_Icc.mp hi).2; omega
  rw [Nat.cast_sub hi', Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp [Fin.sum_univ_two]

end MathlibExt.LinearAlgebra.PowerSumMatrixWanted
