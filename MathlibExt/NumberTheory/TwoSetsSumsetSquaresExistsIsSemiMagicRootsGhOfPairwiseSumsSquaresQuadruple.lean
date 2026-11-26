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
# Quadruple extensions come from two further semi-magic squares

Given a semi-magic square of squares and integers extending the associated triple to a
quadruple with square pairwise sums, the square roots of those sums, arranged in a suitable
order, form two further semi-magic squares of squares. The main result is
`exists_isSemiMagicRoots_gh_of_pairwiseSumsSquares_quadruple`.

Statements from Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
*INTEGERS* 26 (2026), Article A66
(<https://math.colgate.edu/~integers/aa66/aa66.pdf>).
-/

namespace MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

private theorem row_eq_col (e : Fin 3 → Fin 3 → ℤ) (he : IsSemiMagicRoots e) (i j : Fin 3) :
    e i 0 ^ 2 + e i 1 ^ 2 + e i 2 ^ 2 = e 0 j ^ 2 + e 1 j ^ 2 + e 2 j ^ 2 := by
  obtain ⟨_, hrow, hcol⟩ := he
  simpa only [Fin.sum_univ_three] using (hrow i).trans (hcol j).symm

/-- **Quadruple extensions come from two further semi-magic squares.** Let $E = (e_{ij})$ be a
$3 \times 3$ integer matrix whose squared entries $e_{ij}^2$ have all three row sums and all three
column sums equal to one common integer. Put $(a_1, a_2, a_3) = (e_{13}^2, e_{31}^2, e_{22}^2)$ and
$(b_1, b_2, b_3) = (0, e_{21}^2 - e_{13}^2, e_{11}^2 - e_{22}^2)$, and let $a_4, b_4$ be integers
such that every sum $a_i + b_j$ with $1 \le i, j \le 4$ is the square of an integer. Then there
are $3 \times 3$ integer matrices $G = (g_{ij})$ and $H = (h_{ij})$, each of whose squared entries
have all row sums and all column sums equal to one common integer, such that
$g_{12}^2 = e_{12}^2$, $g_{13}^2 = e_{13}^2$, $g_{21}^2 = e_{21}^2$, $g_{31}^2 = e_{31}^2$,
$h_{11}^2 = e_{11}^2$, $h_{22}^2 = e_{22}^2$, $h_{12}^2 = g_{11}^2$, $h_{31}^2 = g_{22}^2$,
$a_4 = g_{22}^2$ and $b_4 = g_{11}^2 - g_{22}^2$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
public theorem exists_isSemiMagicRoots_gh_of_pairwiseSumsSquares_quadruple
    (e : Fin 3 → Fin 3 → ℤ) (he : IsSemiMagicRoots e)
    (a4 b4 : ℤ)
    (h : PairwiseSumsSquares
      ![e 0 2 ^ 2, e 2 0 ^ 2, e 1 1 ^ 2, a4]
      ![0, e 1 0 ^ 2 - e 0 2 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2, b4]) :
    ∃ g h : Fin 3 → Fin 3 → ℤ,
      IsSemiMagicRoots g ∧ IsSemiMagicRoots h ∧
        e 0 1 ^ 2 = g 0 1 ^ 2 ∧ e 0 2 ^ 2 = g 0 2 ^ 2 ∧
          e 1 0 ^ 2 = g 1 0 ^ 2 ∧ e 2 0 ^ 2 = g 2 0 ^ 2 ∧
          e 0 0 ^ 2 = h 0 0 ^ 2 ∧ e 1 1 ^ 2 = h 1 1 ^ 2 ∧
          g 0 0 ^ 2 = h 0 1 ^ 2 ∧ g 1 1 ^ 2 = h 2 0 ^ 2 ∧
          a4 = g 1 1 ^ 2 ∧ b4 = g 0 0 ^ 2 - g 1 1 ^ 2 := by
  -- Choose a square root of every pairwise sum, then arrange the roots so that
  -- every row and every column contains each summand index exactly once.
  have hab' : ∀ i j, ∃ c : ℤ, ![e 0 2 ^ 2, e 2 0 ^ 2, e 1 1 ^ 2, a4] i +
      ![0, e 1 0 ^ 2 - e 0 2 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2, b4] j = c * c := h
  choose r hr using hab'
  have hsq : ∀ i j, (r i j) ^ 2 = ![e 0 2 ^ 2, e 2 0 ^ 2, e 1 1 ^ 2, a4] i +
      ![0, e 1 0 ^ 2 - e 0 2 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2, b4] j := by
    intro i j
    rw [pow_two, ← hr i j]
  have hr00 : (r 0 0) ^ 2 = e 0 2 ^ 2 := by simpa [Matrix.cons_val] using hsq 0 0
  have hr01 : (r 0 1) ^ 2 = e 1 0 ^ 2 := by
    have h01 := hsq 0 1
    simp only [Matrix.cons_val] at h01
    linear_combination h01
  have hr10 : (r 1 0) ^ 2 = e 2 0 ^ 2 := by simpa [Matrix.cons_val] using hsq 1 0
  have hr11 : (r 1 1) ^ 2 = e 0 1 ^ 2 := by
    have h11 := hsq 1 1
    simp only [Matrix.cons_val] at h11
    linear_combination h11 - row_eq_col e he 0 0
  have hr20 : (r 2 0) ^ 2 = e 1 1 ^ 2 := by simpa [Matrix.cons_val] using hsq 2 0
  have hr22 : (r 2 2) ^ 2 = e 0 0 ^ 2 := by
    have h22 := hsq 2 2
    simp only [Matrix.cons_val] at h22
    linear_combination h22
  have hr30 : (r 3 0) ^ 2 = a4 := by simpa [Matrix.cons_val] using hsq 3 0
  have hr33 : (r 3 3) ^ 2 = a4 + b4 := by simpa [Matrix.cons_val] using hsq 3 3
  refine ⟨![![r 3 3, r 1 1, r 0 0], ![r 0 1, r 3 0, r 1 3], ![r 1 0, r 0 3, r 3 1]],
    ![![r 2 2, r 3 3, r 0 0], ![r 0 3, r 2 0, r 3 2], ![r 3 0, r 0 2, r 2 3]],
    ⟨e 2 0 ^ 2 + e 1 0 ^ 2 + a4 + b4, ?_, ?_⟩,
    ⟨e 0 2 ^ 2 + e 0 0 ^ 2 + a4 + b4, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [Fin.sum_univ_three, Matrix.cons_val, hsq] <;> ring1
  · intro j
    fin_cases j <;> simp [Fin.sum_univ_three, Matrix.cons_val, hsq] <;> ring1
  · intro i
    fin_cases i <;> simp [Fin.sum_univ_three, Matrix.cons_val, hsq] <;> ring1
  · intro j
    fin_cases j <;> simp [Fin.sum_univ_three, Matrix.cons_val, hsq] <;> ring1
  · simpa [Matrix.cons_val] using hr11.symm
  · simpa [Matrix.cons_val] using hr00.symm
  · simpa [Matrix.cons_val] using hr01.symm
  · simpa [Matrix.cons_val] using hr10.symm
  · simpa [Matrix.cons_val] using hr22.symm
  · simpa [Matrix.cons_val] using hr20.symm
  · simp
  · simp [Matrix.cons_val]
  · simpa [Matrix.cons_val] using hr30.symm
  · simp only [Matrix.cons_val, hr33, hr30]
    ring1

end MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted
