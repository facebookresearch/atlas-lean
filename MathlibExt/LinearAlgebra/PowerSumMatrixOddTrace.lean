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
import Mathlib.Algebra.BigOperators.Intervals
import MathlibExt.LinearAlgebra.PowerSumMatrixPairTrace

/-!
# Traces for sums of powers with an odd endpoint

For `n = 2s + 1`, set aside the last term and apply `sum_pow_eq_sum_trace_of_even`
to the first `2s` terms.

## References

* Peiran Ding, Yanjun Zhu and Lei Wang, *A New Formula for the Sum of Integer Powers Based on
  Elementary Matrix Theory*, INTEGERS 25 (2025), Article A98, pp. 1–15, Lemma 2 (§2.3, pp. 4–5).
  The even-endpoint decomposition is Lemma 1 (§2.3, p. 4).
  <https://math.colgate.edu/~integers/z98/z98.pdf>
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
  obtain ⟨s, rfl⟩ := hn
  rw [sum_Icc_succ_top (a := 1) (b := 2 * s) (by omega) (fun i ↦ (i : ℝ) ^ k),
    sum_pow_eq_sum_trace_of_even (2 * s) k (even_two_mul s),
    show 2 * s / 2 = s by omega, show (2 * s + 1) / 2 = s by omega]

end MathlibExt.LinearAlgebra.PowerSumMatrixWanted
