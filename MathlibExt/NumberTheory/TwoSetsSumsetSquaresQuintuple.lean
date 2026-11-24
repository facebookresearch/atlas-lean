/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TwoSetsSumsetSquares
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.Basic

/-!
# Five integers with square sums from two semi-magic squares

Two semi-magic squares of integer squares with a common diagonal give five integers whose
sums with three common offsets are all integer squares.
-/

namespace MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

private theorem row_eq_col (e : Fin 3 → Fin 3 → ℤ) (he : IsSemiMagicRoots e) (i j : Fin 3) :
    e i 0 ^ 2 + e i 1 ^ 2 + e i 2 ^ 2 = e 0 j ^ 2 + e 1 j ^ 2 + e 2 j ^ 2 := by
  obtain ⟨_, hrow, hcol⟩ := he
  simpa only [Fin.sum_univ_three] using (hrow i).trans (hcol j).symm

private theorem pairwiseSumsSquares_of_diagonal_offsets
    (e : Fin 3 → Fin 3 → ℤ) (he : IsSemiMagicRoots e) :
    PairwiseSumsSquares
      ![e 0 2 ^ 2, e 2 0 ^ 2, e 1 1 ^ 2]
      ![0, e 2 2 ^ 2 - e 1 1 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2] := by
  let roots : Fin 3 → Fin 3 → ℤ :=
    ![![e 0 2, e 1 0, e 2 1],
      ![e 2 0, e 0 1, e 1 2],
      ![e 1 1, e 2 2, e 0 0]]
  intro i j
  refine ⟨roots i j, ?_⟩
  fin_cases i <;> dsimp [roots, Matrix.cons_val] <;>
    fin_cases j <;> dsimp [Matrix.cons_val] <;> rw [← pow_two]
  · ring1
  · linear_combination -(row_eq_col e he 1 2)
  · linear_combination row_eq_col e he 0 1
  · ring1
  · linear_combination row_eq_col e he 2 1
  · linear_combination -(row_eq_col e he 1 0)
  · ring1
  · ring1
  · ring1

/-- **Five integers with square sums from two semi-magic squares of squares.** Let $e_{ij}$ and
$f_{ij}$, $1 \le i, j \le 3$, be integers such that the matrices of squares $(e_{ij}^2)$ and
$(f_{ij}^2)$ are both semi-magic (in each matrix all row sums and all column sums are equal) and
have the same diagonal, $e_{ii}^2 = f_{ii}^2$ for $i = 1, 2, 3$. Put $a_1 = e_{13}^2$,
$a_2 = e_{31}^2$, $a_3 = e_{22}^2$, $a_4 = f_{13}^2$, $a_5 = f_{31}^2$ and $b_1 = 0$,
$b_2 = e_{21}^2 - e_{13}^2$, $b_3 = e_{11}^2 - e_{22}^2$. Then $a_i + b_j$ is a perfect square for
all $1 \le i \le 5$ and $1 \le j \le 3$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
public theorem pairwiseSumsSquares_quintuple_of_isSemiMagicRoots
    (e f : Fin 3 → Fin 3 → ℤ)
    (he : IsSemiMagicRoots e) (hf : IsSemiMagicRoots f)
    (hdiag : e 0 0 ^ 2 = f 0 0 ^ 2 ∧ e 1 1 ^ 2 = f 1 1 ^ 2 ∧
      e 2 2 ^ 2 = f 2 2 ^ 2) :
    PairwiseSumsSquares
      ![e 0 2 ^ 2, e 2 0 ^ 2, e 1 1 ^ 2, f 0 2 ^ 2, f 2 0 ^ 2]
      ![0, e 1 0 ^ 2 - e 0 2 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2] := by
  -- The offset from the off-diagonal entries is also a difference of diagonal squares.
  have hb : e 1 0 ^ 2 - e 0 2 ^ 2 = e 2 2 ^ 2 - e 1 1 ^ 2 := by
    linear_combination row_eq_col e he 1 2
  have hoffsets :
      ![0, f 2 2 ^ 2 - f 1 1 ^ 2, f 0 0 ^ 2 - f 1 1 ^ 2] =
        ![0, e 2 2 ^ 2 - e 1 1 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2] := by
    rw [hdiag.1, hdiag.2.1, hdiag.2.2]
  have heSums := pairwiseSumsSquares_of_diagonal_offsets e he
  have hfSums := pairwiseSumsSquares_of_diagonal_offsets f hf
  rw [hoffsets] at hfSums
  rw [hb]
  intro i j
  fin_cases i
  · exact heSums 0 j
  · exact heSums 1 j
  · exact heSums 2 j
  · exact hfSums 0 j
  · exact hfSums 1 j

end MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted
