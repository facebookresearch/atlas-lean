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

/-- **Barry's triangle recurrence.** The function $s(\beta, n, k)$ of natural numbers
$\beta, n, k$, with natural-number values, is defined by $s(\beta, 0, 0) = 1$, by
$s(\beta, n, k) = 0$ if exactly one of $n, k$ is $0$, and by
$$s(\beta, n, k) = s(\beta + 1, n - 1, k - 1) + \beta k\, s(\beta, n - 1, k)$$
if $n, k \ge 1$.

The triangle OEIS A080416 is $s(0, n, k)$ for $2 \le k \le n$.

Source: Bulat Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of
Integer Sequences 29 (2026), Article 26.2.8, equation (1). -/
public def barryTriangleAux : ℕ → ℕ → ℕ → ℕ
  | _, 0, 0 => 1
  | _, 0, _ + 1 => 0
  | _, _ + 1, 0 => 0
  | β, n + 1, k + 1 => barryTriangleAux (β + 1) n k + β * (k + 1) * barryTriangleAux β n (k + 1)

/-- **Defining recurrence of Barry's triangle.** For all natural numbers $\beta, n, k$, Barry's
triangle recurrence $s$ satisfies
$s(\beta, n + 1, k + 1) = s(\beta + 1, n, k) + \beta (k + 1)\, s(\beta, n, k + 1)$.

Source: Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of Integer
Sequences 29 (2026), Article 26.2.8, equation (1). -/
public theorem barryTriangleAux_succ_succ (β n k : ℕ) :
    barryTriangleAux β (n + 1) (k + 1) =
      barryTriangleAux (β + 1) n k + β * (k + 1) * barryTriangleAux β n (k + 1) :=
  rfl

/-- **Small values of Barry's triangle.** Barry's triangle recurrence $s$ takes the values
$s(0, 2, 2) = 1$, $s(0, 4, 3) = 4$ and $s(0, 6, 4) = 67$.

Source: Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of Integer
Sequences 29 (2026), Article 26.2.8, Table 1. -/
public theorem barryTriangleAux_small_values :
    barryTriangleAux 0 2 2 = 1 ∧ barryTriangleAux 0 4 3 = 4 ∧ barryTriangleAux 0 6 4 = 67 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **Matrix power formula for Barry's triangle.** Let $s$ be Barry's triangle recurrence and let
$2 \le a \le n$. Let $M$ be the $(a - 1) \times (a - 1)$ lower bidiagonal matrix of natural
numbers with diagonal entries $M_{i,i} = i(a - i)$ for $i = 1, \dots, a - 1$, entries
$M_{i+1,i} = 1$ just below the diagonal, and all other entries $0$. Then $s(0, n, a)$ is the
bottom-left entry $(M^{n-2})_{a-1,1}$ of the power $M^{n-2}$.

Source: Khaidarov, *Enumeration of Certain k-Block Partitions of Barry*, Journal of Integer
Sequences 29 (2026), Article 26.2.8, main result announced in the abstract, equation (7)
(`jis-2026-26.2.8-abstract-main`). -/
public theorem_wanted barryTriangleAux_eq_matrix_pow (n a : ℕ) (ha : 2 ≤ a) (han : a ≤ n) :
    barryTriangleAux 0 n a =
      ((Matrix.of fun i j : Fin (a - 1) =>
          if i = j then ((i : ℕ) + 1) * (a - ((i : ℕ) + 1))
          else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) ^ (n - 2))
        ⟨a - 2, by omega⟩ ⟨0, by omega⟩

/-- **Matrix-free formula for Barry's triangle.** Let $s$ be Barry's triangle recurrence and let
$2 \le a \le n$. Then
$$s(0, n, a) = \sum_{p_1 + \dots + p_{a-1} = n - a} \prod_{i=1}^{a-1} \bigl(i(a - i)\bigr)^{p_i},$$
where the sum runs over all tuples $(p_1, \dots, p_{a-1})$ of natural numbers with sum $n - a$.

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
