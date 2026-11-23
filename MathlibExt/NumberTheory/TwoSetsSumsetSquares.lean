/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring.Basic

/-!
# Two sets whose sumset elements are squares

The two quadruples in Ajai Choudhry's family (5.1) have sixteen square sums.
The proof gives a table of integer square roots, one for each choice of summands.

## References

* Ajai Choudhry, [*Two Sets of Integers Such That All Elements of the Sumset of the Two Sets
  Are Perfect Squares*](https://arxiv.org/abs/2508.07806), Theorem 3.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

/-- **Families whose pairwise sums are squares.** Let $\alpha$ be a type with an addition and a
multiplication, and let $(a_i)_{i \in I}$ and $(b_j)_{j \in J}$ be families in $\alpha$ indexed by
arbitrary types $I$ and $J$. They have all pairwise sums square when, for every $i \in I$ and
$j \in J$, the sum $a_i + b_j$ is a square in $\alpha$, that is, $a_i + b_j = c \cdot c$ for some
$c \in \alpha$. -/
def PairwiseSumsSquares {ι κ α : Type*} [Add α] [Mul α]
    (a : ι → α) (b : κ → α) : Prop :=
  ∀ i j, IsSquare (a i + b j)

/-- **Semi-magic matrix of squares.** A $3 \times 3$ integer matrix $E = (e_{ij})$ has semi-magic
squares when the matrix $(e_{ij}^2)$ of its squared entries is semi-magic: there is an integer
$S$ such that $\sum_{j=1}^{3} e_{ij}^2 = S$ for every row $i$ and $\sum_{i=1}^{3} e_{ij}^2 = S$ for
every column $j$. -/
def IsSemiMagicRoots (e : Fin 3 → Fin 3 → ℤ) : Prop :=
  ∃ S : ℤ,
    (∀ i : Fin 3, ∑ j : Fin 3, (e i j) ^ 2 = S) ∧
      ∀ j : Fin 3, ∑ i : Fin 3, (e i j) ^ 2 = S

/-- **A four-parameter family of integer quadruples with square pairwise sums.** For integers
$u_1, u_2, v_1, v_2$, put $w = v_1^4 - 6 v_1^2 v_2^2 + v_2^4$, $s = v_1^2 + v_2^2$ and
$d = v_1^2 - v_2^2$, and let
$a_1 = w^2 d^2 (u_1^2 + u_2^2)^2$, $a_2 = w^2 s^2 (u_1^2 - u_2^2)^2$,
$a_3 = d^2 (s^2 u_1^2 - 16 u_1 u_2 v_1^2 v_2^2 - s^2 u_2^2)^2$,
$a_4 = d^2 (s^2 u_1^2 + 16 u_1 u_2 v_1^2 v_2^2 - s^2 u_2^2)^2$, $b_1 = 0$,
$b_2 = w^2 \bigl((v_2 - v_1) u_1 + (v_1 + v_2) u_2\bigr)
\bigl((v_1 + v_2) u_1 + (v_1 - v_2) u_2\bigr)\bigl((v_1 - v_2) u_1 + (v_1 + v_2) u_2\bigr)
\bigl((v_1 + v_2) u_1 - (v_1 - v_2) u_2\bigr)$,
$b_3 = -d^2 (s u_1 + 4 u_1 v_1 v_2 - s u_2)(s u_1 - 4 u_1 v_1 v_2 - s u_2)
(s u_1 + 4 u_2 v_1 v_2 + s u_2)(s u_1 - 4 u_2 v_1 v_2 + s u_2)$ and
$b_4 = -d^2 (s u_1 + 4 u_1 v_1 v_2 + s u_2)(s u_1 - 4 u_1 v_1 v_2 + s u_2)
(s u_1 + 4 u_2 v_1 v_2 - s u_2)(s u_1 - 4 u_2 v_1 v_2 - s u_2)$.
Then $a_i + b_j$ is the square of an integer for all $1 \le i, j \le 4$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 3. -/
theorem pairwiseSumsSquares_quadruple_family51
    (u1 u2 v1 v2 : ℤ) :
    PairwiseSumsSquares
      ![(v1 ^ 4 - 6 * v1 ^ 2 * v2 ^ 2 + v2 ^ 4) ^ 2 *
            (v1 ^ 2 - v2 ^ 2) ^ 2 * (u1 ^ 2 + u2 ^ 2) ^ 2,
          (v1 ^ 4 - 6 * v1 ^ 2 * v2 ^ 2 + v2 ^ 4) ^ 2 *
            (v1 ^ 2 + v2 ^ 2) ^ 2 * (u1 ^ 2 - u2 ^ 2) ^ 2,
          (v1 ^ 2 - v2 ^ 2) ^ 2 *
            ((v1 ^ 2 + v2 ^ 2) ^ 2 * u1 ^ 2 -
              16 * u1 * u2 * v1 ^ 2 * v2 ^ 2 -
              (v1 ^ 2 + v2 ^ 2) ^ 2 * u2 ^ 2) ^ 2,
          (v1 ^ 2 - v2 ^ 2) ^ 2 *
            ((v1 ^ 2 + v2 ^ 2) ^ 2 * u1 ^ 2 +
              16 * u1 * u2 * v1 ^ 2 * v2 ^ 2 -
              (v1 ^ 2 + v2 ^ 2) ^ 2 * u2 ^ 2) ^ 2]
      ![0,
        (v1 ^ 4 - 6 * v1 ^ 2 * v2 ^ 2 + v2 ^ 4) ^ 2 *
          ((v2 - v1) * u1 + (v1 + v2) * u2) *
          ((v1 + v2) * u1 + (v1 - v2) * u2) *
          ((v1 - v2) * u1 + (v1 + v2) * u2) *
          ((v1 + v2) * u1 - (v1 - v2) * u2),
        -((v1 ^ 2 - v2 ^ 2) ^ 2) *
          ((v1 ^ 2 + v2 ^ 2) * u1 + 4 * u1 * v1 * v2 -
            (v1 ^ 2 + v2 ^ 2) * u2) *
          ((v1 ^ 2 + v2 ^ 2) * u1 - 4 * u1 * v1 * v2 -
            (v1 ^ 2 + v2 ^ 2) * u2) *
          ((v1 ^ 2 + v2 ^ 2) * u1 + 4 * u2 * v1 * v2 +
            (v1 ^ 2 + v2 ^ 2) * u2) *
          ((v1 ^ 2 + v2 ^ 2) * u1 - 4 * u2 * v1 * v2 +
            (v1 ^ 2 + v2 ^ 2) * u2),
        -((v1 ^ 2 - v2 ^ 2) ^ 2) *
          ((v1 ^ 2 + v2 ^ 2) * u1 + 4 * u1 * v1 * v2 +
            (v1 ^ 2 + v2 ^ 2) * u2) *
          ((v1 ^ 2 + v2 ^ 2) * u1 - 4 * u1 * v1 * v2 +
            (v1 ^ 2 + v2 ^ 2) * u2) *
          ((v1 ^ 2 + v2 ^ 2) * u1 + 4 * u2 * v1 * v2 -
            (v1 ^ 2 + v2 ^ 2) * u2) *
          ((v1 ^ 2 + v2 ^ 2) * u1 - 4 * u2 * v1 * v2 -
            (v1 ^ 2 + v2 ^ 2) * u2)] := by
  let s := v1 ^ 2 + v2 ^ 2
  let d := v1 ^ 2 - v2 ^ 2
  let t := 2 * v1 * v2
  let w := v1 ^ 4 - 6 * v1 ^ 2 * v2 ^ 2 + v2 ^ 4
  let x := u1 ^ 2 - u2 ^ 2
  let y := 2 * u1 * u2
  let z := u1 ^ 2 + u2 ^ 2
  let roots : Fin 4 → Fin 4 → ℤ :=
    ![![w * d * z, w * s * y, d * (2 * t ^ 2 * x + s ^ 2 * y),
          d * (2 * t ^ 2 * x - s ^ 2 * y)],
      ![w * s * x, w * t * z, t * (s ^ 2 * x + 2 * d ^ 2 * y),
          t * (s ^ 2 * x - 2 * d ^ 2 * y)],
      ![d * (s ^ 2 * x - 2 * t ^ 2 * y), t * (2 * d ^ 2 * x - s ^ 2 * y),
          2 * t * d * s * z, 2 * t * d * s * (x - y)],
      ![d * (s ^ 2 * x + 2 * t ^ 2 * y), t * (2 * d ^ 2 * x + s ^ 2 * y),
          2 * t * d * s * (x + y), 2 * t * d * s * z]]
  intro i j
  refine ⟨roots i j, ?_⟩
  fin_cases i <;> dsimp [roots, Matrix.cons_val] <;>
    fin_cases j <;> dsimp [Matrix.cons_val, s, d, t, w, x, y, z] <;> ring1

end MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted
