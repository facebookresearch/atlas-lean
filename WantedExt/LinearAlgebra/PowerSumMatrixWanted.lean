/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A new formula for the sum of integer powers

Statements from Peiran Ding, Yanjun Zhu and Lei Wang,
"A New Formula for the Sum of Integer Powers Based on
Elementary Matrix Theory", *INTEGERS* 25 (2025),
Article A98
(<https://math.colgate.edu/~integers/vol25.html>).

Theorem 1 is the Girard-Waring formula for the trace
of a power of a real `2 × 2` matrix in terms of its
trace and determinant. It is proved in
`MathlibExt.LinearAlgebra.PowerSumMatrix` and re-exported here.
Lemma 3 is the Beta integral
`∫₀¹ x^r (1 - x)^r dx = 1 / ((2r + 1) * C(2r, r))`
for positive integers `r`; it is proved for every `r : ℕ`
(at `r = 0` both sides are `1`) as
`intervalIntegral.integral_pow_one_sub_pow` in
`MathlibExt.Analysis.SpecialFunctions.Gamma.BetaPowerProduct`
and re-exported here.

Lemmas 1 and 2 decompose `S(n, k) = 1^k + ⋯ + n^k`
into traces of `diag(i, 2s + 1 - i)`, `s = ⌊n/2⌋`;
Theorem 2 is the trace formula with
`W(n, r) = ∑_{i=1}^n (i/(n+1))^r (1 - i/(n+1))^r`;
Theorem 3's `≈` (as `n → ∞`) is read as asymptotic
equivalence, the reading used in the paper's proof of
Theorem 4; Theorem 4 is the combinatorial identity.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.Analysis.SpecialFunctions.Gamma.BetaPowerProduct
public import MathlibExt.LinearAlgebra.PowerSumMatrix
public import MathlibExt.LinearAlgebra.PowerSumMatrixOddTrace

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.LinearAlgebra.PowerSumMatrixWanted

/-- **Lemma 1**: for a positive integer `k` and an even
positive integer `n = 2s`,
`1^k + ⋯ + n^k = ∑_{i=1}^s Tr (M_i^k)` with
`M_i = diag(i, 2s + 1 - i)`. Stated for all `n, k ∈ ℕ`
with `n` even (it also holds at `k = 0` and `n = 0`).

Source: Peiran Ding, Yanjun Zhu and Lei Wang, "A New
Formula for the Sum of Integer Powers Based on
Elementary Matrix Theory", INTEGERS 25 (2025), Article A98, Lemma 1 (`integers-2025-A98-lem-1`). -/
theorem_wanted sum_pow_eq_sum_trace_of_even (n k : ℕ)
    (hn : Even n) :
    ∑ i ∈ Finset.Icc 1 n, (i : ℝ) ^ k =
      ∑ i ∈ Finset.Icc 1 (n / 2),
        Matrix.trace
          (Matrix.diagonal ![(i : ℝ), 2 * (n / 2 : ℕ) + 1 - i] ^ k)

/-- **Theorem 2**: for positive integers `k` and `n`,
`S(n, k) = k (n+1)^k / 2 * ∑_{r=0}^{⌊k/2⌋}
  (-1)^r / (k - r) * C(k - r, r) * W(n, r)` with
`W(n, r) = ∑_{i=1}^n (i/(n+1))^r (1 - i/(n+1))^r`
(Section 2.4). Stated for every `n ∈ ℕ` (both sides
vanish at `n = 0`).

Source: Peiran Ding, Yanjun Zhu and Lei Wang, "A New
Formula for the Sum of Integer Powers Based on
Elementary Matrix Theory", INTEGERS 25 (2025), Article A98, Theorem 2
(`integers-2025-A98-thm-2`). -/
theorem_wanted sum_pow_eq_W_formula (n k : ℕ) (hk : 1 ≤ k) :
    ∑ i ∈ Finset.Icc 1 n, (i : ℝ) ^ k =
      (k : ℝ) * ((n : ℝ) + 1) ^ k / 2 *
        ∑ r ∈ Finset.range (k / 2 + 1),
          (-1 : ℝ) ^ r / ((k - r : ℕ) : ℝ) *
            (Nat.choose (k - r) r : ℝ) *
            ∑ i ∈ Finset.Icc 1 n,
              ((i : ℝ) / ((n : ℝ) + 1)) ^ r *
                (1 - (i : ℝ) / ((n : ℝ) + 1)) ^ r

/-- **Theorem 3**: for every positive integer `k`, as
`n → ∞`,
`S(n, k) ≈ k (n+1)^(k+1) / 2 * ∑_{r=0}^{⌊k/2⌋}
  (-1)^r / ((k - r)(2r + 1)) * C(k - r, r) / C(2r, r)`,
with `≈` read as asymptotic equivalence (ratio tending
to `1`), as in the paper's proof of Theorem 4; the
difference of the two sides is not `o(1)`.

Source: Peiran Ding, Yanjun Zhu and Lei Wang, "A New
Formula for the Sum of Integer Powers Based on
Elementary Matrix Theory", INTEGERS 25 (2025), Article A98, Theorem 3
(`integers-2025-A98-thm-3`). -/
theorem_wanted sum_pow_isEquivalent (k : ℕ) (hk : 1 ≤ k) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n, (i : ℝ) ^ k)
      (fun n : ℕ => (k : ℝ) * ((n : ℝ) + 1) ^ (k + 1) / 2 *
        ∑ r ∈ Finset.range (k / 2 + 1),
          (-1 : ℝ) ^ r / (((k - r : ℕ) : ℝ) * (2 * r + 1)) *
            ((Nat.choose (k - r) r : ℝ) /
              (Nat.choose (2 * r) r : ℝ)))

/-- **Theorem 4**: for every positive integer `k`,
`∑_{r=0}^{⌊k/2⌋} (-1)^r / ((k - r)(2r + 1)) * C(k - r, r)
  * C(2r, r)^(-1) = 2 / (k (k + 1))`. Stated for all
`k ∈ ℕ`: at `k = 0` both sides are `0` under division by
zero.

Source: Peiran Ding, Yanjun Zhu and Lei Wang, "A New
Formula for the Sum of Integer Powers Based on
Elementary Matrix Theory", INTEGERS 25 (2025), Article A98, Theorem 4
(`integers-2025-A98-thm-4`). -/
theorem_wanted sum_choose_div_choose_eq (k : ℕ) :
    ∑ r ∈ Finset.range (k / 2 + 1),
        (-1 : ℚ) ^ r / (((k - r : ℕ) : ℚ) * (2 * r + 1)) *
          (Nat.choose (k - r) r : ℚ) *
          (Nat.choose (2 * r) r : ℚ)⁻¹ =
      2 / ((k : ℚ) * (k + 1))

end MathlibExt.LinearAlgebra.PowerSumMatrixWanted
