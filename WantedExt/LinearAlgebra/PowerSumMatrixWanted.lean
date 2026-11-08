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
trace and determinant; both parities were verified
exactly over random rational matrices for `m ≤ 5`.
Lemma 3 is the Beta integral
`∫₀¹ x^r (1 - x)^r dx = 1 / ((2r + 1) * C(2r, r))`.

Not stated (see the source audit table): Lemmas 1
and 2 (their matrices survive only as flattened
fragments), Theorem 2 (`W(n, r)` is defined in a
missing section), Theorem 3 (an approximation
without an error term) and Theorem 4 (whose identity
could not be pinned from the extraction).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.LinearAlgebra.PowerSumMatrixWanted

/-- **Theorem 1**: for any positive integer `m` and
any `2 × 2` real-valued matrix `M`,
`Tr (M ^ (2m)) = 2m * ∑_{r=0}^m (-1)^r *
  (2m - r - 1)! / (r! (2m - 2r)!) *
  (Det M)^r * (Tr M)^(2m - 2r)` and
`Tr (M ^ (2m+1)) = (2m + 1) * ∑_{r=0}^m (-1)^r *
  (2m - r)! / (r! (2m + 1 - 2r)!) *
  (Det M)^r * (Tr M)^(2m + 1 - 2r)`.

Source: Peiran Ding, Yanjun Zhu and Lei Wang, "A New
Formula for the Sum of Integer Powers Based on
Elementary Matrix Theory", Theorem 1, equations (5)
and (6). -/
theorem_wanted trace_pow_two (M : Matrix (Fin 2) (Fin 2) ℝ)
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
            M.det ^ r * Matrix.trace M ^ (2 * m + 1 - 2 * r)

/-- **Lemma 3**: for every positive integer `r`
(indeed every `r`, including `0`),
`∫₀¹ x^r (1 - x)^r dx = 1 / ((2r + 1) * C(2r, r))`.

Source: Peiran Ding, Yanjun Zhu and Lei Wang, "A New
Formula for the Sum of Integer Powers Based on
Elementary Matrix Theory", Lemma 3. -/
theorem_wanted integral_pow_one_sub_pow (r : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ r * (1 - x) ^ r) =
      1 / ((2 * r + 1 : ℝ) * (Nat.choose (2 * r) r : ℝ))

end MathlibExt.LinearAlgebra.PowerSumMatrixWanted
