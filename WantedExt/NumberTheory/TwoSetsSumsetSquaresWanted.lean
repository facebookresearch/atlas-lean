/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Two sets whose sumset elements are squares

Statements from Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
*INTEGERS* 26 (2026), Article A66
(<https://math.colgate.edu/~integers/aa66/aa66.pdf>).

Finite families are indexed by `Fin m` and `Fin n`; the paper's
one-based index `1` is Lean index `0` here.  A `3 × 3` matrix with
squared entries is represented by its integer roots
`e : Fin 3 → Fin 3 → ℤ`, with matrix entries `(e i j)^2`.
Semi-magic means all row sums and all column sums of those squared
entries have one common value.

Lemma 2 is split into the actual construction and converse
statements used in its proof, rather than the bare existence
formulation.  This avoids a vacuous reading in which both sides are
satisfied independently by zero examples: the forward parts start
from given semi-magic root matrices, and the converse parts produce
the matrices `E₁`, `F₁`, `G₁`, and `H₁` built from the pairwise
sums in the paper's proof.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Rat.Defs

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

/-- All pairwise sums of two finite families are squares. -/
def PairwiseSumsSquares {ι κ α : Type*} [Add α] [Mul α]
    (a : ι → α) (b : κ → α) : Prop :=
  ∀ i j, IsSquare (a i + b j)

/-- The squared-entry matrix `(e i j)^2` is semi-magic: all row and
column sums have a common value. -/
def IsSemiMagicRoots (e : Fin 3 → Fin 3 → ℤ) : Prop :=
  ∃ S : ℤ,
    (∀ i : Fin 3, ∑ j : Fin 3, (e i j) ^ 2 = S) ∧
      ∀ j : Fin 3, ∑ i : Fin 3, (e i j) ^ 2 = S

/-- **Lemma 1**: rational families with all pairwise sums squares
can be rescaled and translated to integer families, by
`aᵢ' = k²aᵢ - t` and `bⱼ' = k²bⱼ + t`, whenever the displayed
values are integers.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 1. -/
theorem_wanted exists_int_pairwiseSumsSquares_scale_translate
    (m n : ℕ) (a : Fin m → ℚ) (b : Fin n → ℚ)
    (hab : PairwiseSumsSquares a b)
    (t : ℤ) (k : ℚ)
    (ha : ∀ i, ∃ z : ℤ, (z : ℚ) = k ^ 2 * a i - (t : ℚ))
    (hb : ∀ j, ∃ z : ℤ, (z : ℚ) = k ^ 2 * b j + (t : ℚ)) :
    ∃ a' : Fin m → ℤ, ∃ b' : Fin n → ℤ,
      (∀ i, (a' i : ℚ) = k ^ 2 * a i - (t : ℚ)) ∧
        (∀ j, (b' j : ℚ) = k ^ 2 * b j + (t : ℚ)) ∧
        PairwiseSumsSquares a' b'

/-- **Lemma 2, triple construction**: from a semi-magic
squared-entry matrix with roots `e`, the triples in formula (2.2)
have all nine pairwise sums squares.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
theorem_wanted pairwiseSumsSquares_triple_of_isSemiMagicRoots
    (e : Fin 3 → Fin 3 → ℤ) (he : IsSemiMagicRoots e) :
    PairwiseSumsSquares
      ![e 0 2 ^ 2, e 2 0 ^ 2, e 1 1 ^ 2]
      ![0, e 1 0 ^ 2 - e 0 2 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2]

/-- **Lemma 2, triple converse**: from two integer triples with all
nine pairwise sums squares, the matrix `E₁` in formula (2.9) has
integer square roots and is semi-magic.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
theorem_wanted exists_isSemiMagicRoots_of_pairwiseSumsSquares_triple
    (a b : Fin 3 → ℤ) (hab : PairwiseSumsSquares a b) :
    ∃ e : Fin 3 → Fin 3 → ℤ,
      IsSemiMagicRoots e ∧
        e 0 0 ^ 2 = a 2 + b 2 ∧ e 0 1 ^ 2 = a 1 + b 1 ∧
          e 0 2 ^ 2 = a 0 + b 0 ∧ e 1 0 ^ 2 = a 0 + b 1 ∧
          e 1 1 ^ 2 = a 2 + b 0 ∧ e 1 2 ^ 2 = a 1 + b 2 ∧
          e 2 0 ^ 2 = a 1 + b 0 ∧ e 2 1 ^ 2 = a 0 + b 2 ∧
          e 2 2 ^ 2 = a 2 + b 1

/-- **Lemma 2, quintuple construction**: if `E` and `F` are
semi-magic and their diagonal squared entries agree as in (2.3),
then adjoining `a₄ = f₁₃²` and `a₅ = f₃₁²` to the triple from
`E` gives all fifteen pairwise sums squares.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
theorem_wanted pairwiseSumsSquares_quintuple_of_isSemiMagicRoots
    (e f : Fin 3 → Fin 3 → ℤ)
    (he : IsSemiMagicRoots e) (hf : IsSemiMagicRoots f)
    (hdiag : e 0 0 ^ 2 = f 0 0 ^ 2 ∧ e 1 1 ^ 2 = f 1 1 ^ 2 ∧
      e 2 2 ^ 2 = f 2 2 ^ 2) :
    PairwiseSumsSquares
      ![e 0 2 ^ 2, e 2 0 ^ 2, e 1 1 ^ 2, f 0 2 ^ 2, f 2 0 ^ 2]
      ![0, e 1 0 ^ 2 - e 0 2 ^ 2, e 0 0 ^ 2 - e 1 1 ^ 2]

/-- **Lemma 2, quintuple converse**: relative to the triples built
from a given semi-magic `E`, any two further integers making all
fifteen sums squares arise from a semi-magic `F` satisfying (2.3)
and formula (2.4).

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
theorem_wanted exists_isSemiMagicRoots_f_of_pairwiseSumsSquares_quintuple
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

/-- **Lemma 2, quadruple construction**: if `E`, `G`, and `H` are
semi-magic and satisfy conditions (2.5), (2.6), and (2.7), then
adjoining `a₄ = g₂₂²` and `b₄ = g₁₁² - g₂₂²` as in (2.8)
gives all sixteen pairwise sums squares.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
theorem_wanted pairwiseSumsSquares_quadruple_of_isSemiMagicRoots
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
        g 0 0 ^ 2 - g 1 1 ^ 2]

/-- **Lemma 2, quadruple converse**: relative to the triples built
from a given semi-magic `E`, any further `a₄, b₄` making all
sixteen sums squares arise from semi-magic `G` and `H` satisfying
(2.5), (2.6), (2.7), and formula (2.8).

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Lemma 2. -/
theorem_wanted exists_isSemiMagicRoots_gh_of_pairwiseSumsSquares_quadruple
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
          a4 = g 1 1 ^ 2 ∧ b4 = g 0 0 ^ 2 - g 1 1 ^ 2

/-- **Theorem 1, family (3.1)**: the first four-parameter pair of
integer triples with all pairwise sums squares.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 1. -/
theorem_wanted pairwiseSumsSquares_triple_family31
    (p q r s : ℤ) :
    PairwiseSumsSquares
      ![0, 16 * p * q * r * s,
        (p + q + r + s) * (p + q - r - s) * (p - q + r - s) *
          (p - q - r + s)]
      ![4 * (p * r - q * s) ^ 2, 4 * (p * s - q * r) ^ 2,
        4 * (p * q - r * s) ^ 2]

/-- **Theorem 1, family (3.2)**: the second four-parameter pair of
integer triples with all pairwise sums squares.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 1. -/
theorem_wanted pairwiseSumsSquares_triple_family32
    (p q r s : ℤ) :
    PairwiseSumsSquares
      ![-(p + q + r + s) * (p + q - r - s) * (p - q + r - s) *
          (p - q - r + s),
        -(p - q + r + s) * (p - q - r - s) * (p + q + r - s) *
          (p + q - r + s), 0]
      ![(p ^ 2 - q ^ 2 + r ^ 2 - s ^ 2) ^ 2,
        (p ^ 2 - q ^ 2 - r ^ 2 + s ^ 2) ^ 2,
        (p ^ 2 + q ^ 2 - r ^ 2 - s ^ 2) ^ 2]

/-- **Theorem 1, family (3.3)**: the third four-parameter pair of
integer triples with all pairwise sums squares.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 1. -/
theorem_wanted pairwiseSumsSquares_triple_family33
    (p q r s : ℤ) :
    PairwiseSumsSquares
      ![4 * (p * s - q * r) ^ 2, 4 * (p * s + q * r) ^ 2,
        (p ^ 2 - q ^ 2 - r ^ 2 + s ^ 2) ^ 2]
      ![4 * (p ^ 2 - q ^ 2) * (r ^ 2 - s ^ 2), 0,
        4 * (p ^ 2 - r ^ 2) * (q ^ 2 - s ^ 2)]

/-- **Theorem 2**: the seven-parameter rational quintuple/triple
family (4.1) with all fifteen pairwise sums squares of rationals.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 2. -/
theorem_wanted pairwiseSumsSquares_quintuple_family41
    (f g m u1 u2 v1 v2 : ℚ) :
    PairwiseSumsSquares
      ![4 * (m * u1 * u2 * (u1 * v1 - u2 * v2) * f ^ 2 -
            (u1 * v2 - u2 * v1) * (m ^ 2 * u1 * u2 * v1 * v2 - 1) *
              f * g -
            m * v1 * v2 * (u1 * v1 - u2 * v2) * g ^ 2) ^ 2,
        4 * (m * u1 * u2 * (u1 * v1 + u2 * v2) * f ^ 2 +
            (u1 * v2 + u2 * v1) * (m ^ 2 * u1 * u2 * v1 * v2 + 1) *
              f * g +
            m * v1 * v2 * (u1 * v1 + u2 * v2) * g ^ 2) ^ 2,
        ((u1 ^ 2 * u2 ^ 2 * (v1 ^ 2 - v2 ^ 2) * m ^ 2 +
              u1 ^ 2 - u2 ^ 2) * f ^ 2 -
            (v1 ^ 2 * v2 ^ 2 * (u1 ^ 2 - u2 ^ 2) * m ^ 2 +
              v1 ^ 2 - v2 ^ 2) * g ^ 2) ^ 2,
        4 * (m * u1 * u2 * (u1 * v1 - u2 * v2) * f ^ 2 +
            (u1 * v2 - u2 * v1) * (m ^ 2 * u1 * u2 * v1 * v2 - 1) *
              f * g -
            m * v1 * v2 * (u1 * v1 - u2 * v2) * g ^ 2) ^ 2,
        4 * (m * u1 * u2 * (u1 * v1 + u2 * v2) * f ^ 2 -
            (u1 * v2 + u2 * v1) * (m ^ 2 * u1 * u2 * v1 * v2 + 1) *
              f * g +
            m * v1 * v2 * (u1 * v1 + u2 * v2) * g ^ 2) ^ 2]
      ![0,
        -4 * (u1 ^ 2 - u2 ^ 2) * (v1 ^ 2 - v2 ^ 2) *
          (m ^ 2 * u1 ^ 2 * u2 ^ 2 * f ^ 2 - g ^ 2) *
          (f ^ 2 - m ^ 2 * v1 ^ 2 * v2 ^ 2 * g ^ 2),
        4 * (m ^ 2 * u1 ^ 2 * v1 ^ 2 - 1) *
          (m ^ 2 * u2 ^ 2 * v2 ^ 2 - 1) *
          (f ^ 2 * u1 ^ 2 - g ^ 2 * v1 ^ 2) *
          (f ^ 2 * u2 ^ 2 - g ^ 2 * v2 ^ 2)]

/-- **Theorem 3**: the four-parameter pair of integer quadruples
(5.1) with all sixteen pairwise sums perfect squares.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 3. -/
theorem_wanted pairwiseSumsSquares_quadruple_family51
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
            (v1 ^ 2 + v2 ^ 2) * u2)]

/-- **Theorem 4, family (5.8)**: the first three-parameter pair of
rational quadruples with all sixteen pairwise sums squares.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 4. -/
theorem_wanted pairwiseSumsSquares_quadruple_family58
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
            (m ^ 4 - 2 * m ^ 3 + 6 * m - 1) * r)]

/-- **Theorem 4, family (5.9)**: the second three-parameter pair of
rational quadruples with all sixteen pairwise sums squares.

Source: Ajai Choudhry, "Two Sets of Integers Such That All
Elements of the Sumset of the Two Sets Are Perfect Squares",
Theorem 4. -/
theorem_wanted pairwiseSumsSquares_quadruple_family59
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
          ((m ^ 3 - 3 * m) * q + (3 * m ^ 2 - 1) * r)]

end TwoSetsSumsetSquaresWanted
