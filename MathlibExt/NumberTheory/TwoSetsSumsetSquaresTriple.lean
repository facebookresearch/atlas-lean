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
import Mathlib.Tactic.Linarith

/-!
# Triples with square pairwise sums and semi-magic squares

Given a semi-magic square of integer squares, `pairwiseSumsSquares_triple_of_isSemiMagicRoots`
constructs two triples whose nine pairwise sums are the nine squares in the matrix.
Conversely, `exists_isSemiMagicRoots_of_pairwiseSumsSquares_triple` arranges the square roots of
nine square pairwise sums into a semi-magic square of squares.
-/

namespace MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

/-- **Triples with square pairwise sums from a semi-magic square of squares.** Let $e_{ij}$,
$1 \le i, j \le 3$, be integers such that the matrix of squares $(e_{ij}^2)$ is semi-magic, that
is, all its row sums and all its column sums are equal. Put $a_1 = e_{13}^2$, $a_2 = e_{31}^2$,
$a_3 = e_{22}^2$ and $b_1 = 0$, $b_2 = e_{21}^2 - e_{13}^2$, $b_3 = e_{11}^2 - e_{22}^2$. Then
$a_i + b_j$ is a perfect square for all $i, j \in \{1, 2, 3\}$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
public theorem pairwiseSumsSquares_triple_of_isSemiMagicRoots
    (e : Fin 3 → Fin 3 → ℤ) (he : IsSemiMagicRoots e) :
    PairwiseSumsSquares
      ![e 0 2 ^ 2, e 2 0 ^ 2, e 1 1 ^ 2]
      ![0, e 1 0 ^ 2 - e 0 2 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2] := by
  obtain ⟨S, hrow, hcol⟩ := he
  simp only [Fin.sum_univ_three] at hrow hcol
  -- The sums are a rearrangement of the squared entries of `e`.
  let roots : Fin 3 → Fin 3 → ℤ :=
    ![![e 0 2, e 1 0, e 2 1], ![e 2 0, e 0 1, e 1 2], ![e 1 1, e 2 2, e 0 0]]
  intro i j
  refine ⟨roots i j, ?_⟩
  fin_cases i <;> dsimp [roots, Matrix.cons_val] <;>
    fin_cases j <;> dsimp [Matrix.cons_val] <;> rw [← pow_two] <;>
    linarith only [hrow 0, hrow 1, hrow 2, hcol 0, hcol 1, hcol 2]

/-- **Triples with square pairwise sums come from semi-magic squares.** Let $a_1, a_2, a_3$ and
$b_1, b_2, b_3$ be integers such that every sum $a_i + b_j$ is the square of an integer. Then
there is a $3 \times 3$ integer matrix $E = (e_{ij})$ whose squared entries $e_{ij}^2$ have all
three row sums and all three column sums equal to one common integer, and such that
$e_{11}^2 = a_3 + b_3$, $e_{12}^2 = a_2 + b_2$, $e_{13}^2 = a_1 + b_1$, $e_{21}^2 = a_1 + b_2$,
$e_{22}^2 = a_3 + b_1$, $e_{23}^2 = a_2 + b_3$, $e_{31}^2 = a_2 + b_1$, $e_{32}^2 = a_1 + b_3$ and
$e_{33}^2 = a_3 + b_2$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
public theorem exists_isSemiMagicRoots_of_pairwiseSumsSquares_triple
    (a b : Fin 3 → ℤ) (hab : PairwiseSumsSquares a b) :
    ∃ e : Fin 3 → Fin 3 → ℤ,
      IsSemiMagicRoots e ∧
        e 0 0 ^ 2 = a 2 + b 2 ∧ e 0 1 ^ 2 = a 1 + b 1 ∧
          e 0 2 ^ 2 = a 0 + b 0 ∧ e 1 0 ^ 2 = a 0 + b 1 ∧
          e 1 1 ^ 2 = a 2 + b 0 ∧ e 1 2 ^ 2 = a 1 + b 2 ∧
          e 2 0 ^ 2 = a 1 + b 0 ∧ e 2 1 ^ 2 = a 0 + b 2 ∧
          e 2 2 ^ 2 = a 2 + b 1 := by
  -- Choose a square root of every pairwise sum, then arrange the roots so that
  -- every row and every column contains each summand index exactly once.
  have hab' : ∀ i j, ∃ c : ℤ, a i + b j = c * c := hab
  choose r hr using hab'
  have hsq : ∀ i j, (r i j) ^ 2 = a i + b j := by
    intro i j
    rw [pow_two, ← hr i j]
  refine ⟨![![r 2 2, r 1 1, r 0 0],
      ![r 0 1, r 2 0, r 1 2],
      ![r 1 0, r 0 2, r 2 1]],
    ⟨∑ i, a i + ∑ j, b j, ?_, ?_⟩,
    hsq 2 2, hsq 1 1, hsq 0 0, hsq 0 1, hsq 2 0, hsq 1 2, hsq 1 0, hsq 0 2,
    hsq 2 1⟩
  · intro i
    fin_cases i <;> simp [Fin.sum_univ_three, Matrix.cons_val, hsq] <;> ac_rfl
  · intro j
    fin_cases j <;> simp [Fin.sum_univ_three, Matrix.cons_val, hsq] <;> ac_rfl

end MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted
