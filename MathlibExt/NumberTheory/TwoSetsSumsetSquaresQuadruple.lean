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
# Four integers with square sums from three semi-magic squares

Three semi-magic squares of integer squares, linked by equalities between some of their entries,
give four integers and four offsets whose pairwise sums are all integer squares. Every such sum is
an entry of one of the three squares.

## References

* Ajai Choudhry, [*Two Sets of Integers Such That All Elements of the Sumset of the Two Sets
  Are Perfect Squares*](https://arxiv.org/abs/2508.07806), Lemma 2.
-/

namespace MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

/-- The six row and column equations of a semi-magic matrix of squares, written out. -/
private theorem isSemiMagicRoots_rows_cols (e : Fin 3 → Fin 3 → ℤ) (he : IsSemiMagicRoots e) :
    ∃ S : ℤ,
      e 0 0 ^ 2 + e 0 1 ^ 2 + e 0 2 ^ 2 = S ∧ e 1 0 ^ 2 + e 1 1 ^ 2 + e 1 2 ^ 2 = S ∧
        e 2 0 ^ 2 + e 2 1 ^ 2 + e 2 2 ^ 2 = S ∧ e 0 0 ^ 2 + e 1 0 ^ 2 + e 2 0 ^ 2 = S ∧
        e 0 1 ^ 2 + e 1 1 ^ 2 + e 2 1 ^ 2 = S ∧ e 0 2 ^ 2 + e 1 2 ^ 2 + e 2 2 ^ 2 = S := by
  obtain ⟨S, hrow, hcol⟩ := he
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | simpa only [Fin.sum_univ_three] using hrow _
    | simpa only [Fin.sum_univ_three] using hcol _

/-- **Extending the triples to quadruples with square pairwise sums.** Let $E = (e_{ij})$,
$G = (g_{ij})$ and $H = (h_{ij})$ be $3 \times 3$ integer matrices, each of whose squared entries
have all three row sums and all three column sums equal to one common integer, such that
$e_{12}^2 = g_{12}^2$, $e_{13}^2 = g_{13}^2$, $e_{21}^2 = g_{21}^2$, $e_{31}^2 = g_{31}^2$,
$e_{11}^2 = h_{11}^2$, $e_{22}^2 = h_{22}^2$, $g_{11}^2 = h_{12}^2$ and $g_{22}^2 = h_{31}^2$. Put
$(a_1, a_2, a_3, a_4) = (e_{13}^2, e_{31}^2, e_{22}^2, g_{22}^2)$ and
$(b_1, b_2, b_3, b_4) = (0, e_{21}^2 - e_{13}^2, e_{11}^2 - e_{22}^2, g_{11}^2 - g_{22}^2)$. Then
$a_i + b_j$ is the square of an integer for all $1 \le i, j \le 4$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
public theorem pairwiseSumsSquares_quadruple_of_isSemiMagicRoots
    (e g h : Fin 3 → Fin 3 → ℤ)
    (he : IsSemiMagicRoots e) (hg : IsSemiMagicRoots g)
    (hh : IsSemiMagicRoots h)
    (h25 : e 0 1 ^ 2 = g 0 1 ^ 2 ∧ e 0 2 ^ 2 = g 0 2 ^ 2 ∧
      e 1 0 ^ 2 = g 1 0 ^ 2 ∧ e 2 0 ^ 2 = g 2 0 ^ 2)
    (h26 : e 0 0 ^ 2 = h 0 0 ^ 2 ∧ e 1 1 ^ 2 = h 1 1 ^ 2)
    (h27 : g 0 0 ^ 2 = h 0 1 ^ 2 ∧ g 1 1 ^ 2 = h 2 0 ^ 2) :
    PairwiseSumsSquares
      ![e 0 2 ^ 2, e 2 0 ^ 2, e 1 1 ^ 2, g 1 1 ^ 2]
      ![0, e 1 0 ^ 2 - e 0 2 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2,
        g 0 0 ^ 2 - g 1 1 ^ 2] := by
  obtain ⟨_, he₁, he₂, he₃, he₄, he₅, he₆⟩ := isSemiMagicRoots_rows_cols e he
  obtain ⟨_, hg₁, hg₂, hg₃, hg₄, hg₅, hg₆⟩ := isSemiMagicRoots_rows_cols g hg
  obtain ⟨_, hh₁, hh₂, hh₃, hh₄, hh₅, hh₆⟩ := isSemiMagicRoots_rows_cols h hh
  obtain ⟨-, h₂, h₃, h₄⟩ := h25
  obtain ⟨h₅, h₆⟩ := h26
  obtain ⟨h₇, h₈⟩ := h27
  -- Each sum is the square of an entry of `e`, `g` or `h`; the row and column equations of the
  -- three matrices, together with the linking equalities, make each identity linear in the squares.
  let roots : Fin 4 → Fin 4 → ℤ :=
    ![![e 0 2, e 1 0, e 2 1, g 2 1],
      ![e 2 0, e 0 1, e 1 2, g 1 2],
      ![e 1 1, e 2 2, e 0 0, h 2 2],
      ![g 1 1, g 2 2, h 1 2, g 0 0]]
  intro i j
  refine ⟨roots i j, ?_⟩
  fin_cases i <;> dsimp [roots, Matrix.cons_val] <;>
    fin_cases j <;> dsimp [Matrix.cons_val] <;> rw [← pow_two] <;> linarith

end MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted
