/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresQuintuple
public import MathlibExt.NumberTheory.TwoSetsSumsetSquaresTriple
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Quintuple extensions from a second semi-magic square

A quintuple with square pairwise sums yields a second semi-magic matrix of squares with the
same diagonal and the prescribed two off-diagonal entries.

## References

* Ajai Choudhry, "Two Sets of Integers Such That All Elements of the Sumset of the Two Sets
  Are Perfect Squares", *INTEGERS* 26 (2026), Article A66,
  <https://math.colgate.edu/~integers/aa66/aa66.pdf>, Lemma 2.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

/-- **Quintuple extensions come from a second semi-magic square.** Let $E = (e_{ij})$ be a
$3 \times 3$ integer matrix whose squared entries $e_{ij}^2$ have all three row sums and all three
column sums equal to one common integer. Put $(a_1, a_2, a_3) = (e_{13}^2, e_{31}^2, e_{22}^2)$ and
$(b_1, b_2, b_3) = (0, e_{21}^2 - e_{13}^2, e_{11}^2 - e_{22}^2)$, and let $a_4, a_5$ be integers
such that every sum $a_i + b_j$ with $1 \le i \le 5$ and $1 \le j \le 3$ is the square of an
integer. Then there is a $3 \times 3$ integer matrix $F = (f_{ij})$ whose squared entries also
have all row sums and all column sums equal to one common integer, with $f_{11}^2 = e_{11}^2$,
$f_{22}^2 = e_{22}^2$, $f_{33}^2 = e_{33}^2$, $a_4 = f_{13}^2$ and $a_5 = f_{31}^2$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
theorem exists_isSemiMagicRoots_f_of_pairwiseSumsSquares_quintuple
    (e : Fin 3 → Fin 3 → ℤ) (he : IsSemiMagicRoots e)
    (a4 a5 : ℤ)
    (h : PairwiseSumsSquares
      ![e 0 2 ^ 2, e 2 0 ^ 2, e 1 1 ^ 2, a4, a5]
      ![0, e 1 0 ^ 2 - e 0 2 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2]) :
    ∃ f : Fin 3 → Fin 3 → ℤ,
      IsSemiMagicRoots f ∧
        e 0 0 ^ 2 = f 0 0 ^ 2 ∧ e 1 1 ^ 2 = f 1 1 ^ 2 ∧
          e 2 2 ^ 2 = f 2 2 ^ 2 ∧
          a4 = f 0 2 ^ 2 ∧ a5 = f 2 0 ^ 2
    := by
  have hab : PairwiseSumsSquares
      ![a4, a5, e 1 1 ^ 2]
      ![0, e 1 0 ^ 2 - e 0 2 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2] := by
    intro i j
    fin_cases i
    · exact h 3 j
    · exact h 4 j
    · exact h 2 j
  obtain ⟨f, hf, h00, -, h02, -, h11, -, h20, -, h22⟩ :=
    exists_isSemiMagicRoots_of_pairwiseSumsSquares_triple _ _ hab
  dsimp [Matrix.cons_val] at h00 h02 h11 h20 h22
  obtain ⟨_, hrow, hcol⟩ := he
  have hrc : e 1 0 ^ 2 + e 1 1 ^ 2 + e 1 2 ^ 2 =
      e 0 2 ^ 2 + e 1 2 ^ 2 + e 2 2 ^ 2 := by
    simpa only [Fin.sum_univ_three] using (hrow 1).trans (hcol 2).symm
  refine ⟨f, hf, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination -h00
  · simpa only [add_zero] using h11.symm
  · linear_combination -hrc - h22
  · simpa only [add_zero] using h02.symm
  · simpa only [add_zero] using h20.symm

end MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted
