/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Matrix.Mul

/-!
# Explicit formulas for Barry's triangle A080416

Wanted statements from Khaidarov on the Stirling-like triangle OEIS A080416, given by the
recurrence `s(β, n, k)` derived from Corcino et al. The paper (whose abstract is the corpus
record) proves a matrix formula and a matrix-free formula for `s(0, n, a)`. Its closing
generalization to weighted North-East lattice paths is not stated here.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The three-parameter recurrence behind OEIS A080416: `s(β, 0, 0) = 1`,
`s(β, n, k) = 0` if exactly one of `n, k` is `0`, and
`s(β, n, k) = s(β + 1, n - 1, k - 1) + β k s(β, n - 1, k)` otherwise. The triangle
A080416 is `s(0, n, k)` for `2 ≤ k ≤ n`.

Source: Bulat Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of
Integer Sequences 29 (2026), Article 26.2.8, equation (1). -/
public def barryTriangleAux : ℕ → ℕ → ℕ → ℕ
  | _, 0, 0 => 1
  | _, 0, _ + 1 => 0
  | _, _ + 1, 0 => 0
  | β, n + 1, k + 1 => barryTriangleAux (β + 1) n k + β * (k + 1) * barryTriangleAux β n (k + 1)

/-- The defining recurrence `s(β, n + 1, k + 1) = s(β + 1, n, k) + β (k + 1) s(β, n, k + 1)`.

Source: Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of Integer
Sequences 29 (2026), Article 26.2.8, equation (1). -/
public theorem barryTriangleAux_succ_succ (β n k : ℕ) :
    barryTriangleAux β (n + 1) (k + 1) =
      barryTriangleAux (β + 1) n k + β * (k + 1) * barryTriangleAux β n (k + 1) :=
  rfl

/-- Values from the paper's Table 1: `s(0, 2, 2) = 1`, `s(0, 4, 3) = 4`, `s(0, 6, 4) = 67`.

Source: Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of Integer
Sequences 29 (2026), Article 26.2.8, Table 1. -/
public theorem barryTriangleAux_small_values :
    barryTriangleAux 0 2 2 = 1 ∧ barryTriangleAux 0 4 3 = 4 ∧ barryTriangleAux 0 6 4 = 67 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Main result, matrix form (equation (7)): for `2 ≤ a ≤ n`, `s(0, n, a)` is the bottom-left
entry of `A ^ (n - 2)`, where `A` is the `(a - 1) × (a - 1)` lower bidiagonal matrix with
diagonal entries `i (a - i)` (`i = 1, …, a - 1`) and subdiagonal entries `1`.

Source: Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of Integer
Sequences 29 (2026), Article 26.2.8, main result announced in the abstract, equation (7)
(`jis-2026-26.2.8-abstract-main`). -/
public theorem_wanted barryTriangleAux_eq_matrix_pow (n a : ℕ) (ha : 2 ≤ a) (han : a ≤ n) :
    barryTriangleAux 0 n a =
      ((Matrix.of fun i j : Fin (a - 1) =>
          if i = j then ((i : ℕ) + 1) * (a - ((i : ℕ) + 1))
          else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) ^ (n - 2))
        ⟨a - 2, by omega⟩ ⟨0, by omega⟩

/-- Main result, matrix-free form (equation (11)): for `2 ≤ a ≤ n`,
`s(0, n, a) = ∑_{p₁ + ⋯ + p_{a-1} = n - a} ∏_{i=1}^{a-1} (i (a - i))^{pᵢ}`, the sum over
tuples of nonnegative integers. Index `i : Fin (a - 1)` stands for the paper's `i + 1`.

Source: Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of Integer
Sequences 29 (2026), Article 26.2.8, main result announced in the abstract, equation (11)
(`jis-2026-26.2.8-abstract-main`). -/
public theorem_wanted barryTriangleAux_eq_sum_antidiagonalTuple (n a : ℕ) (ha : 2 ≤ a)
    (han : a ≤ n) :
    barryTriangleAux 0 n a =
      ∑ p ∈ Finset.Nat.antidiagonalTuple (a - 1) (n - a),
        ∏ i : Fin (a - 1), (((i : ℕ) + 1) * (a - ((i : ℕ) + 1))) ^ p i

end

end MetaMathlibExt
