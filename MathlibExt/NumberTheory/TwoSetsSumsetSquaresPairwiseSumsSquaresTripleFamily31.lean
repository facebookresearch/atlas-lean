/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TwoSetsSumsetSquares
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring.Basic

/-!
# Four-parameter triples with square pairwise sums, family (3.1)

`pairwiseSumsSquares_triple_family31` states that for all integers $p, q, r, s$, putting
$a_1 = 0$, $a_2 = 16pqrs$, $a_3 = (p+q+r+s)(p+q-r-s)(p-q+r-s)(p-q-r+s)$ and
$b_1 = 4(pr-qs)^2$, $b_2 = 4(ps-qr)^2$, $b_3 = 4(pq-rs)^2$, every sum $a_i + b_j$ is the
square of an integer. The proof exhibits the nine roots explicitly.

## References

* Statements from Ajai Choudhry, "Two Sets of Integers Such That All Elements of the Sumset
  of the Two Sets Are Perfect Squares", *INTEGERS* 26 (2026), Article A66
  (<https://math.colgate.edu/~integers/aa66/aa66.pdf>), Theorem 1.
-/

namespace MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

/-- **Four-parameter triples with square pairwise sums, family (3.1).** For all integers
$p, q, r, s$, put $a_1 = 0$, $a_2 = 16pqrs$, $a_3 = (p+q+r+s)(p+q-r-s)(p-q+r-s)(p-q-r+s)$ and
$b_1 = 4(pr - qs)^2$, $b_2 = 4(ps - qr)^2$, $b_3 = 4(pq - rs)^2$. Then $a_i + b_j$ is a perfect
square for all $i, j \in \{1, 2, 3\}$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 1. -/
public theorem pairwiseSumsSquares_triple_family31
    (p q r s : ℤ) :
    PairwiseSumsSquares
      ![0, 16 * p * q * r * s,
        (p + q + r + s) * (p + q - r - s) * (p - q + r - s) *
          (p - q - r + s)]
      ![4 * (p * r - q * s) ^ 2, 4 * (p * s - q * r) ^ 2,
        4 * (p * q - r * s) ^ 2] := by
  let roots : Fin 3 → Fin 3 → ℤ :=
    ![![2 * (p * r - q * s), 2 * (p * s - q * r), 2 * (p * q - r * s)],
      ![2 * (p * r + q * s), 2 * (p * s + q * r), 2 * (p * q + r * s)],
      ![p ^ 2 - q ^ 2 + r ^ 2 - s ^ 2, p ^ 2 - q ^ 2 - r ^ 2 + s ^ 2,
        p ^ 2 + q ^ 2 - r ^ 2 - s ^ 2]]
  intro i j
  refine ⟨roots i j, ?_⟩
  fin_cases i <;> dsimp [roots, Matrix.cons_val] <;>
    fin_cases j <;> dsimp [Matrix.cons_val] <;> ring1

end MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted
