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
public import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.Basic

/-!
# Two sets whose sumset elements are squares

Ajai Choudhry's integer triples and quadruples and his two three-parameter families of rational
quadruples have square pairwise sums. The proofs give a square root for each choice of summands.
His Lemma 1, `exists_int_pairwiseSumsSquares_scale_translate`, scales two rational families with
square pairwise sums by $k^2$ and shifts them by $-t$ and $+t$: when the results are integers,
their pairwise sums are squares of integers.

## References

* Ajai Choudhry, [*Two Sets of Integers Such That All Elements of the Sumset of the Two Sets
  Are Perfect Squares*](https://arxiv.org/abs/2508.07806), Lemma 1 and Theorems 1, 3 and 4.
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

/-- **Scaling rational families with square pairwise sums to integers.** Let $a_1, \dots, a_m$
and $b_1, \dots, b_n$ be rational numbers such that every sum $a_i + b_j$ is the square of a
rational number, and let $t$ be an integer and $k$ a rational number such that $k^2 a_i - t$ is an
integer for every $i$ and $k^2 b_j + t$ is an integer for every $j$. Then the integers
$a_i' = k^2 a_i - t$ and $b_j' = k^2 b_j + t$ are such that every sum $a_i' + b_j'$ is the square
of an integer.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 1. -/
theorem exists_int_pairwiseSumsSquares_scale_translate
    (m n : ℕ) (a : Fin m → ℚ) (b : Fin n → ℚ)
    (hab : PairwiseSumsSquares a b)
    (t : ℤ) (k : ℚ)
    (ha : ∀ i, ∃ z : ℤ, (z : ℚ) = k ^ 2 * a i - (t : ℚ))
    (hb : ∀ j, ∃ z : ℤ, (z : ℚ) = k ^ 2 * b j + (t : ℚ)) :
    ∃ a' : Fin m → ℤ, ∃ b' : Fin n → ℤ,
      (∀ i, (a' i : ℚ) = k ^ 2 * a i - (t : ℚ)) ∧
        (∀ j, (b' j : ℚ) = k ^ 2 * b j + (t : ℚ)) ∧
        PairwiseSumsSquares a' b' := by
  choose a' ha' using ha
  choose b' hb' using hb
  refine ⟨a', b', ha', hb', fun i j ↦ ?_⟩
  -- The shifts cancel: `a' i + b' j = k ^ 2 * (a i + b j) = (k * r) ^ 2`, and a rational square
  -- that is an integer is the square of an integer.
  obtain ⟨r, hr⟩ := hab i j
  refine Rat.isSquare_intCast_iff.mp ⟨k * r, ?_⟩
  push_cast
  rw [ha' i, hb' j]
  linear_combination k ^ 2 * hr

/-- **Four-parameter triples with square pairwise sums, family (3.2).** For all integers
$p, q, r, s$, put $a_1 = -(p+q+r+s)(p+q-r-s)(p-q+r-s)(p-q-r+s)$,
$a_2 = -(p-q+r+s)(p-q-r-s)(p+q+r-s)(p+q-r+s)$, $a_3 = 0$ and
$b_1 = (p^2 - q^2 + r^2 - s^2)^2$, $b_2 = (p^2 - q^2 - r^2 + s^2)^2$,
$b_3 = (p^2 + q^2 - r^2 - s^2)^2$. Then $a_i + b_j$ is a perfect square for all
$i, j \in \{1, 2, 3\}$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 1. -/
theorem pairwiseSumsSquares_triple_family32
    (p q r s : ℤ) :
    PairwiseSumsSquares
      ![-(p + q + r + s) * (p + q - r - s) * (p - q + r - s) *
          (p - q - r + s),
        -(p - q + r + s) * (p - q - r - s) * (p + q + r - s) *
          (p + q - r + s), 0]
      ![(p ^ 2 - q ^ 2 + r ^ 2 - s ^ 2) ^ 2,
        (p ^ 2 - q ^ 2 - r ^ 2 + s ^ 2) ^ 2,
        (p ^ 2 + q ^ 2 - r ^ 2 - s ^ 2) ^ 2] := by
  -- The same table of roots as for family (3.3): its squares form a semi-magic square.
  let roots : Fin 3 → Fin 3 → ℤ :=
    ![![2 * (p * r - q * s), 2 * (p * s - q * r), 2 * (p * q - r * s)],
      ![2 * (p * r + q * s), 2 * (p * s + q * r), 2 * (p * q + r * s)],
      ![p ^ 2 - q ^ 2 + r ^ 2 - s ^ 2, p ^ 2 - q ^ 2 - r ^ 2 + s ^ 2,
        p ^ 2 + q ^ 2 - r ^ 2 - s ^ 2]]
  intro i j
  refine ⟨roots i j, ?_⟩
  fin_cases i <;> dsimp [roots, Matrix.cons_val] <;>
    fin_cases j <;> dsimp [Matrix.cons_val] <;> ring1

/-- **Four-parameter triples with square pairwise sums, family (3.3).** For all integers
$p, q, r, s$, put $a_1 = 4(ps - qr)^2$, $a_2 = 4(ps + qr)^2$, $a_3 = (p^2 - q^2 - r^2 + s^2)^2$
and $b_1 = 4(p^2 - q^2)(r^2 - s^2)$, $b_2 = 0$, $b_3 = 4(p^2 - r^2)(q^2 - s^2)$. Then $a_i + b_j$
is a perfect square for all $i, j \in \{1, 2, 3\}$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 1. -/
theorem pairwiseSumsSquares_triple_family33
    (p q r s : ℤ) :
    PairwiseSumsSquares
      ![4 * (p * s - q * r) ^ 2, 4 * (p * s + q * r) ^ 2,
        (p ^ 2 - q ^ 2 - r ^ 2 + s ^ 2) ^ 2]
      ![4 * (p ^ 2 - q ^ 2) * (r ^ 2 - s ^ 2), 0,
        4 * (p ^ 2 - r ^ 2) * (q ^ 2 - s ^ 2)] := by
  let roots : Fin 3 → Fin 3 → ℤ :=
    ![![2 * (p * r - q * s), 2 * (p * s - q * r), 2 * (p * q - r * s)],
      ![2 * (p * r + q * s), 2 * (p * s + q * r), 2 * (p * q + r * s)],
      ![p ^ 2 - q ^ 2 + r ^ 2 - s ^ 2, p ^ 2 - q ^ 2 - r ^ 2 + s ^ 2,
        p ^ 2 + q ^ 2 - r ^ 2 - s ^ 2]]
  intro i j
  refine ⟨roots i j, ?_⟩
  fin_cases i <;> dsimp [roots, Matrix.cons_val] <;>
    fin_cases j <;> dsimp [Matrix.cons_val] <;> ring1

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

/-- **First three-parameter family of rational quadruples with square pairwise sums.** For
rational numbers $m, q, r$, let
$a_1 = 16 m^2 (m^4 - 1)^2 \bigl((5m^4 - 2m^2 + 1) q^2 - 2(m^4 - 6m^2 + 1) q r +
(m^4 - 2m^2 + 5) r^2\bigr)^2$,
$a_2 = 16 m^2 (m^4 - 1)^2 \bigl((5m^4 - 2m^2 + 1) q^2 - (m^4 - 2m^2 + 5) r^2\bigr)^2$,
$a_3 = 16 m^2 (m^4 - 1)^2 \bigl((7m^4 - 2m^2 - 1) q^2 - (2m^4 - 12m^2 + 2) q r -
(m^4 + 2m^2 - 7) r^2\bigr)^2$,
$a_4 = (m^2 - 1)^2 \bigl((3m^8 + 40m^6 - 26m^4 - 1) q^2 + 2(m^4 - 6m^2 + 1)^2 q r -
(m^8 + 26m^4 - 40m^2 - 3) r^2\bigr)^2$,
$b_1 = 0$,
$b_2 = -4 m^2 \bigl((m^4 + 6m^2 - 3) q + (m^4 - 2m^2 + 5) r\bigr)
\bigl((3m^4 - 6m^2 - 1) q - (m^4 - 2m^2 + 5) r\bigr)
\bigl((5m^4 - 2m^2 + 1) q - (3m^4 - 6m^2 - 1) r\bigr)
\bigl((5m^4 - 2m^2 + 1) q + (m^4 + 6m^2 - 3) r\bigr)$,
$b_3 = -128 m^2 (m^4 - 1)^3 (q^2 - r^2)(3m^2 q - m^2 r - q + 3r)(m^2 q + r)$ and
$b_4 = 16 (m^2 + 1)^2 (m^2 - 1)^3 (m^2 q^2 - r^2)
\bigl((m^4 + 6m^3 - 2m - 1) q - (m^4 + 2m^3 - 6m - 1) r\bigr)
\bigl((m^4 - 6m^3 + 2m - 1) q - (m^4 - 2m^3 + 6m - 1) r\bigr)$.
Then $a_i + b_j$ is the square of a rational number for all $1 \le i, j \le 4$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 4. -/
theorem pairwiseSumsSquares_quadruple_family58
    (m q r : ℚ) :
    PairwiseSumsSquares
      ![16 * m ^ 2 * (m ^ 4 - 1) ^ 2 *
            ((5 * m ^ 4 - 2 * m ^ 2 + 1) * q ^ 2 -
              2 * (m ^ 4 - 6 * m ^ 2 + 1) * q * r +
              (m ^ 4 - 2 * m ^ 2 + 5) * r ^ 2) ^ 2,
          16 * m ^ 2 * (m ^ 4 - 1) ^ 2 *
            ((5 * m ^ 4 - 2 * m ^ 2 + 1) * q ^ 2 -
              (m ^ 4 - 2 * m ^ 2 + 5) * r ^ 2) ^ 2,
          16 * m ^ 2 * (m ^ 4 - 1) ^ 2 *
            ((7 * m ^ 4 - 2 * m ^ 2 - 1) * q ^ 2 -
              (2 * m ^ 4 - 12 * m ^ 2 + 2) * q * r -
              (m ^ 4 + 2 * m ^ 2 - 7) * r ^ 2) ^ 2,
          (m ^ 2 - 1) ^ 2 *
            ((3 * m ^ 8 + 40 * m ^ 6 - 26 * m ^ 4 - 1) * q ^ 2 +
              2 * (m ^ 4 - 6 * m ^ 2 + 1) ^ 2 * q * r -
              (m ^ 8 + 26 * m ^ 4 - 40 * m ^ 2 - 3) * r ^ 2) ^ 2]
      ![0,
        -4 * m ^ 2 * ((m ^ 4 + 6 * m ^ 2 - 3) * q +
              (m ^ 4 - 2 * m ^ 2 + 5) * r) *
          ((3 * m ^ 4 - 6 * m ^ 2 - 1) * q -
            (m ^ 4 - 2 * m ^ 2 + 5) * r) *
          ((5 * m ^ 4 - 2 * m ^ 2 + 1) * q -
            (3 * m ^ 4 - 6 * m ^ 2 - 1) * r) *
          ((5 * m ^ 4 - 2 * m ^ 2 + 1) * q +
            (m ^ 4 + 6 * m ^ 2 - 3) * r),
        -128 * m ^ 2 * (m ^ 4 - 1) ^ 3 * (q ^ 2 - r ^ 2) *
          (3 * m ^ 2 * q - m ^ 2 * r - q + 3 * r) * (m ^ 2 * q + r),
        16 * (m ^ 2 + 1) ^ 2 * (m ^ 2 - 1) ^ 3 *
          (m ^ 2 * q ^ 2 - r ^ 2) *
          ((m ^ 4 + 6 * m ^ 3 - 2 * m - 1) * q -
            (m ^ 4 + 2 * m ^ 3 - 6 * m - 1) * r) *
          ((m ^ 4 - 6 * m ^ 3 + 2 * m - 1) * q -
            (m ^ 4 - 2 * m ^ 3 + 6 * m - 1) * r)] := by
  let d := m ^ 2 - 1
  let s := m ^ 2 + 1
  let c := m ^ 4 - 6 * m ^ 2 + 1
  let k := 4 * m * d * s
  -- Each root is a linear combination of these three quadratic forms in x and y.
  let x := 2 * (m ^ 2 * q + r)
  let y := d * (q - r)
  let u := x ^ 2 - y ^ 2
  let v := 2 * x * y
  let w := x ^ 2 + y ^ 2
  let roots : Fin 4 → Fin 4 → ℚ :=
    ![![k * w, 2 * m * (s ^ 2 * u - 2 * d ^ 2 * v),
        k * (u - v), d * (8 * m ^ 2 * u - s ^ 2 * v)],
      ![2 * m * (2 * d ^ 2 * u + s ^ 2 * v), 2 * m * c * w,
        2 * m * (2 * d ^ 2 * u - s ^ 2 * v), s * c * v],
      ![k * (u + v), 2 * m * (s ^ 2 * u + 2 * d ^ 2 * v),
        k * w, d * (8 * m ^ 2 * u + s ^ 2 * v)],
      ![d * (s ^ 2 * u + 8 * m ^ 2 * v), s * c * u,
        d * (s ^ 2 * u - 8 * m ^ 2 * v), d * c * w]]
  intro i j
  refine ⟨roots i j, ?_⟩
  fin_cases i <;> dsimp [roots, Matrix.cons_val] <;>
    fin_cases j <;> dsimp [Matrix.cons_val, u, v, w, x, y, k, c, d, s] <;> grobner

/-- **Second three-parameter family of rational quadruples with square pairwise sums.** For
rational numbers $m, q, r$, let
$a_1 = 16 m^2 (m^4 - 1)^2 \bigl((m^6 - 2m^4 + 5m^2) q^2 + (2m^5 - 12m^3 + 2m) q r +
(5m^4 - 2m^2 + 1) r^2\bigr)^2$,
$a_2 = 16 m^2 (m^4 - 1)^2 \bigl((m^6 - 2m^4 + 5m^2) q^2 - (5m^4 - 2m^2 + 1) r^2\bigr)^2$,
$a_3 = (m^2 - 1)^2 \bigl((m^{10} + 26m^6 - 40m^4 - 3m^2) q^2 +
(2m^9 - 24m^7 + 76m^5 - 24m^3 + 2m) q r - (3m^8 + 40m^6 - 26m^4 - 1) r^2\bigr)^2$,
$a_4 = 16 m^2 (m^4 - 1)^2 \bigl((m^6 + 2m^4 - 7m^2) q^2 - (2m^5 - 12m^3 + 2m) q r -
(7m^4 - 2m^2 - 1) r^2\bigr)^2$,
$b_1 = 0$,
$b_2 = -4 m^2 \bigl((m^5 + 6m^3 - 3m) q - (5m^4 - 2m^2 + 1) r\bigr)
\bigl((3m^5 - 6m^3 - m) q + (5m^4 - 2m^2 + 1) r\bigr)
\bigl((m^5 - 2m^3 + 5m) q + (3m^4 - 6m^2 - 1) r\bigr)
\bigl((m^5 - 2m^3 + 5m) q - (m^4 + 6m^2 - 3) r\bigr)$,
$b_3 = -16 m^2 (m^2 + 1)^2 (m^2 - 1)^3 (q^2 - r^2)
\bigl((m^5 - 2m^4 + 6m^2 - m) q + (m^4 - 6m^3 + 2m - 1) r\bigr)
\bigl((m^5 + 2m^4 - 6m^2 - m) q + (m^4 + 6m^3 - 2m - 1) r\bigr)$ and
$b_4 = 128 m^3 (m^4 - 1)^3 (m r - q)(m^2 q^2 - r^2)\bigl((m^3 - 3m) q + (3m^2 - 1) r\bigr)$.
Then $a_i + b_j$ is the square of a rational number for all $1 \le i, j \le 4$.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 4. -/
theorem pairwiseSumsSquares_quadruple_family59
    (m q r : ℚ) :
    PairwiseSumsSquares
      ![16 * m ^ 2 * (m ^ 4 - 1) ^ 2 *
            ((m ^ 6 - 2 * m ^ 4 + 5 * m ^ 2) * q ^ 2 +
              (2 * m ^ 5 - 12 * m ^ 3 + 2 * m) * q * r +
              (5 * m ^ 4 - 2 * m ^ 2 + 1) * r ^ 2) ^ 2,
          16 * m ^ 2 * (m ^ 4 - 1) ^ 2 *
            ((m ^ 6 - 2 * m ^ 4 + 5 * m ^ 2) * q ^ 2 -
              (5 * m ^ 4 - 2 * m ^ 2 + 1) * r ^ 2) ^ 2,
          (m ^ 2 - 1) ^ 2 *
            ((m ^ 10 + 26 * m ^ 6 - 40 * m ^ 4 - 3 * m ^ 2) * q ^ 2 +
              (2 * m ^ 9 - 24 * m ^ 7 + 76 * m ^ 5 - 24 * m ^ 3 +
                2 * m) * q * r -
              (3 * m ^ 8 + 40 * m ^ 6 - 26 * m ^ 4 - 1) * r ^ 2) ^ 2,
          16 * m ^ 2 * (m ^ 4 - 1) ^ 2 *
            ((m ^ 6 + 2 * m ^ 4 - 7 * m ^ 2) * q ^ 2 -
              (2 * m ^ 5 - 12 * m ^ 3 + 2 * m) * q * r -
              (7 * m ^ 4 - 2 * m ^ 2 - 1) * r ^ 2) ^ 2]
      ![0,
        -4 * m ^ 2 * ((m ^ 5 + 6 * m ^ 3 - 3 * m) * q -
              (5 * m ^ 4 - 2 * m ^ 2 + 1) * r) *
          ((3 * m ^ 5 - 6 * m ^ 3 - m) * q +
            (5 * m ^ 4 - 2 * m ^ 2 + 1) * r) *
          ((m ^ 5 - 2 * m ^ 3 + 5 * m) * q +
            (3 * m ^ 4 - 6 * m ^ 2 - 1) * r) *
          ((m ^ 5 - 2 * m ^ 3 + 5 * m) * q -
            (m ^ 4 + 6 * m ^ 2 - 3) * r),
        -16 * m ^ 2 * (m ^ 2 + 1) ^ 2 * (m ^ 2 - 1) ^ 3 *
          (q ^ 2 - r ^ 2) *
          ((m ^ 5 - 2 * m ^ 4 + 6 * m ^ 2 - m) * q +
            (m ^ 4 - 6 * m ^ 3 + 2 * m - 1) * r) *
          ((m ^ 5 + 2 * m ^ 4 - 6 * m ^ 2 - m) * q +
            (m ^ 4 + 6 * m ^ 3 - 2 * m - 1) * r),
        128 * m ^ 3 * (m ^ 4 - 1) ^ 3 * (m * r - q) *
          (m ^ 2 * q ^ 2 - r ^ 2) *
          ((m ^ 3 - 3 * m) * q + (3 * m ^ 2 - 1) * r)] := by
  let d := m ^ 2 - 1
  let s := m ^ 2 + 1
  let c := m ^ 4 - 6 * m ^ 2 + 1
  let k := 4 * m * d * s
  -- The quadratic form shared by the four diagonal roots.
  let w := (m ^ 6 - 2 * m ^ 4 + 5 * m ^ 2) * q ^ 2 + (2 * m ^ 5 - 12 * m ^ 3 + 2 * m) * q * r +
    (5 * m ^ 4 - 2 * m ^ 2 + 1) * r ^ 2
  -- The quadratic forms in the remaining roots, named by the position of their root.
  let w01 := (m ^ 10 - 8 * m ^ 8 + 18 * m ^ 6 - 32 * m ^ 4 + 5 * m ^ 2) * q ^ 2 +
    (10 * m ^ 9 - 24 * m ^ 7 + 60 * m ^ 5 - 24 * m ^ 3 + 10 * m) * q * r +
    (5 * m ^ 8 - 32 * m ^ 6 + 18 * m ^ 4 - 8 * m ^ 2 + 1) * r ^ 2
  let w02 := (m ^ 5 - 6 * m ^ 3 + m) * q ^ 2 + (m ^ 6 + 3 * m ^ 4 + 3 * m ^ 2 + 1) * q * r +
    (m ^ 5 - 6 * m ^ 3 + m) * r ^ 2
  let w03 := (m ^ 6 - 6 * m ^ 4 + m ^ 2) * q ^ 2 + (6 * m ^ 5 - 4 * m ^ 3 + 6 * m) * q * r +
    (m ^ 4 - 6 * m ^ 2 + 1) * r ^ 2
  let w10 := (m ^ 6 - 2 * m ^ 4 + 5 * m ^ 2) * q ^ 2 - (5 * m ^ 4 - 2 * m ^ 2 + 1) * r ^ 2
  let w13 := (m ^ 6 - 6 * m ^ 4 + m ^ 2) * q ^ 2 + (4 * m ^ 5 - 4 * m) * q * r -
    (m ^ 4 - 6 * m ^ 2 + 1) * r ^ 2
  let w20 := (m ^ 10 + 26 * m ^ 6 - 40 * m ^ 4 - 3 * m ^ 2) * q ^ 2 +
    (2 * m ^ 9 - 24 * m ^ 7 + 76 * m ^ 5 - 24 * m ^ 3 + 2 * m) * q * r -
    (3 * m ^ 8 + 40 * m ^ 6 - 26 * m ^ 4 - 1) * r ^ 2
  let w21 := (m * q - r) * ((m ^ 3 - 3 * m) * q + (3 * m ^ 2 - 1) * r)
  let w23 := (m ^ 10 - 38 * m ^ 6 + 24 * m ^ 4 - 3 * m ^ 2) * q ^ 2 +
    (2 * m ^ 9 + 40 * m ^ 7 - 52 * m ^ 5 + 40 * m ^ 3 + 2 * m) * q * r -
    (3 * m ^ 8 - 24 * m ^ 6 + 38 * m ^ 4 - 1) * r ^ 2
  let w30 := (m ^ 6 + 2 * m ^ 4 - 7 * m ^ 2) * q ^ 2 -
    (2 * m ^ 5 - 12 * m ^ 3 + 2 * m) * q * r - (7 * m ^ 4 - 2 * m ^ 2 - 1) * r ^ 2
  let w31 := (m ^ 10 + 8 * m ^ 8 - 30 * m ^ 6 + 16 * m ^ 4 - 11 * m ^ 2) * q ^ 2 -
    (6 * m ^ 9 - 40 * m ^ 7 + 36 * m ^ 5 - 40 * m ^ 3 + 6 * m) * q * r -
    (11 * m ^ 8 - 16 * m ^ 6 + 30 * m ^ 4 - 8 * m ^ 2 - 1) * r ^ 2
  let w32 := (3 * m ^ 5 - 6 * m ^ 3 - m) * q ^ 2 -
    (m ^ 6 - 5 * m ^ 4 - 5 * m ^ 2 + 1) * q * r - (m ^ 5 + 6 * m ^ 3 - 3 * m) * r ^ 2
  let roots : Fin 4 → Fin 4 → ℚ :=
    ![![k * w, 2 * m * w01, k * w02, k * w03],
      ![k * w10, 2 * m * c * w, k * c * (m * q + r) * (q - m * r), k * w13],
      ![d * w20, s ^ 2 * c * w21, d * c * w, d * w23],
      ![k * w30, 2 * m * w31, k * w32, k * w]]
  intro i j
  refine ⟨roots i j, ?_⟩
  fin_cases i <;> dsimp [roots, Matrix.cons_val] <;> fin_cases j <;>
    dsimp [Matrix.cons_val, k, c, d, s, w, w01, w02, w03, w10, w13, w20, w21, w23, w30, w31,
      w32] <;> ring1

end MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted
