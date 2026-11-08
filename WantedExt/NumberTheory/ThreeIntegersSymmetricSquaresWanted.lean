/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Three integers whose symmetric functions are squares

Source: Ajai Choudhry, *Three Integers Whose Sum, Product, and the Sum of the
Products of the Integers, Taken Two at a Time, Are Perfect Squares*, INTEGERS,
volume 26, paper A35.  The PDF is
https://math.colgate.edu/~integers/aa35/aa35.pdf.

The paper considers `a + b + c`, `a*b + b*c + c*a`, and `a*b*c`.  Lemma 1 is
about rational sums of two rational squares.  Lemma 2 sends `(a,b,c)` to
`(a*b,b*c,c*a)`.  Lemma 3 includes the rescaling of a rational solution to an
integer solution whose entries are sums of two integer squares.

Theorem 1 has four two-parameter families.  Theorem 2 has four families in
which all three entries are themselves squares.  Theorem 3 has one family in
which all three entries are sums of two **nonzero** integer squares.

The parameter values in Theorems 1 and 2 are arbitrary integers, matching
the source; `IsSquare` includes the value `0`.  Theorem 3 is stated in the
nondegenerate range used in its proof.  The printed words "arbitrary integer
parameters" cannot be read literally for the stronger nonzero-square
conclusion: at `(r,s) = (0,1)`, family (3.34) gives entries `0`, `1`, and
`0`.  We therefore assume `r ≠ 0` and `s ≠ 0`.  The degree-eight factor
that occurs as a denominator in Equation (3.38) is then automatically
nonzero: if it vanished, `x = (r / s)^2` would be a positive rational
root of the monic polynomial `x^4 + 2*x^3 - 12*x^2 - 6*x - 1`; the
rational-root theorem leaves only `x = 1`, where the value is `-16`.
For nonzero `r` and `s`, the degree-six and degree-twelve factors below
are positive because every displayed monomial term is positive.

The ambiguous exponent in Family (3.30), where the third entry is
`64*m^4*n^4*(m^2 - n^2)^4`, was pinned against the tabulated example
`(m,n) = (1,2)`, which gives `11025`, `19600`, and `82944`.  With exponent
`2` instead of `4`, the displayed `82944` would be wrong.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Rat.Defs

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

/-- The three elementary symmetric functions of `a`, `b`, and `c` are squares. -/
def HasSquareElementarySymmetricFunctions (a b c : ℤ) : Prop :=
  IsSquare (a + b + c) ∧
    IsSquare (a * b + b * c + c * a) ∧
    IsSquare (a * b * c)

/-- The rational analogue of the square symmetric-function condition. -/
def HasSquareElementarySymmetricFunctionsℚ (a b c : ℚ) : Prop :=
  IsSquare (a + b + c) ∧
    IsSquare (a * b + b * c + c * a) ∧
    IsSquare (a * b * c)

/-- A rational is a sum of two rational squares. -/
def IsSumTwoSquaresℚ (q : ℚ) : Prop :=
  ∃ x y : ℚ, q = x ^ 2 + y ^ 2

/-- An integer is a sum of two integer squares. -/
def IsSumTwoSquaresℤ (z : ℤ) : Prop :=
  ∃ x y : ℤ, z = x ^ 2 + y ^ 2

/-- An integer is a sum of two squares of nonzero integers. -/
def IsSumTwoNonzeroSquaresℤ (z : ℤ) : Prop :=
  ∃ x y : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ z = x ^ 2 + y ^ 2

/-- **Lemma 1**: a ratio of two nonzero rational sums of two squares is a sum
of two rational squares.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the Integers, Taken Two at a Time, Are Perfect Squares", Lemma 1. -/
theorem_wanted sum_two_squares_div_sum_two_squaresℚ
    {α β : ℚ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hα₂ : IsSumTwoSquaresℚ α) (hβ₂ : IsSumTwoSquaresℚ β) :
    IsSumTwoSquaresℚ (α / β)

/-- **Lemma 2**: the pairwise products of a solution form another solution.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the Integers, Taken Two at a Time, Are Perfect Squares", Lemma 2. -/
theorem_wanted hasSquareElementarySymmetricFunctions_pairwise_products
    {a b c : ℤ}
    (h : HasSquareElementarySymmetricFunctions a b c) :
    HasSquareElementarySymmetricFunctions (a * b) (b * c) (c * a)

/-- **Lemma 3**: every entry of a rational solution is a sum of two rational
squares, and scaling the rational solution gives an integer solution whose
entries are integer sums of two squares.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the Integers, Taken Two at a Time, Are Perfect Squares", Lemma 3. -/
theorem_wanted isSumTwoSquaresℚ_of_hasSquareElementarySymmetricFunctionsℚ_and_scaling
    {a b c : ℚ}
    (h : HasSquareElementarySymmetricFunctionsℚ a b c) :
    IsSumTwoSquaresℚ a ∧
      IsSumTwoSquaresℚ b ∧
      IsSumTwoSquaresℚ c ∧
      ∃ (k : ℚ) (A B C : ℤ),
        k ≠ 0 ∧
          (A : ℚ) = k * a ∧
          (B : ℚ) = k * b ∧
          (C : ℚ) = k * c ∧
          HasSquareElementarySymmetricFunctions A B C ∧
          IsSumTwoSquaresℤ A ∧
          IsSumTwoSquaresℤ B ∧
          IsSumTwoSquaresℤ C

private abbrev firstShiftedSextic (s t : ℤ) : ℤ :=
  s ^ 6 - s ^ 4 * t ^ 2 - 5 * s ^ 2 * t ^ 4 + t ^ 6

private abbrev secondShiftedSextic (s t : ℤ) : ℤ :=
  3 * s ^ 6 + s ^ 4 * t ^ 2 + s ^ 2 * t ^ 4 - t ^ 6

/-- **Theorem 1, family (3.3)**.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the Integers, Taken Two at a Time, Are Perfect Squares", Theorem 1, family (3.3). -/
theorem_wanted hasSquareElementarySymmetricFunctions_family33
    (s t : ℤ) :
    HasSquareElementarySymmetricFunctions
      (t ^ 2 * (s ^ 2 - t ^ 2) ^ 2 * (s ^ 2 + t ^ 2))
      (s ^ 2 * (s ^ 2 - t ^ 2) ^ 2 * (s ^ 2 + t ^ 2))
      (4 * s ^ 4 * t ^ 4)

/-- **Theorem 1, family (3.4)**.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the Integers, Taken Two at a Time, Are Perfect Squares", Theorem 1, family (3.4). -/
theorem_wanted hasSquareElementarySymmetricFunctions_family34
    (s t : ℤ) :
    HasSquareElementarySymmetricFunctions
      (4 * s ^ 4 * t ^ 2 * (s ^ 2 + t ^ 2))
      (4 * s ^ 2 * t ^ 4 * (s ^ 2 + t ^ 2))
      ((s ^ 4 - t ^ 4) ^ 2)

/-- **Theorem 1, family (3.5)**.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the Integers, Taken Two at a Time, Are Perfect Squares", Theorem 1, family (3.5). -/
theorem_wanted hasSquareElementarySymmetricFunctions_family35
    (s t : ℤ) :
    HasSquareElementarySymmetricFunctions
      (4 * s ^ 4 * t ^ 2 * (s ^ 2 + t ^ 2) *
        (firstShiftedSextic s t) ^ 2)
      ((s ^ 4 - t ^ 4) ^ 2 * (firstShiftedSextic s t) ^ 2)
      (4 * s ^ 2 * t ^ 4 * (s ^ 2 + t ^ 2) *
        (secondShiftedSextic s t) ^ 2)

/-- **Theorem 1, family (3.6)**.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the Integers, Taken Two at a Time, Are Perfect Squares", Theorem 1, family (3.6). -/
theorem_wanted hasSquareElementarySymmetricFunctions_family36
    (s t : ℤ) :
    HasSquareElementarySymmetricFunctions
      (t ^ 2 * (s ^ 2 - t ^ 2) ^ 2 * (s ^ 2 + t ^ 2) *
        (secondShiftedSextic s t) ^ 2)
      (4 * s ^ 4 * t ^ 4 * (secondShiftedSextic s t) ^ 2)
      (s ^ 2 * (s ^ 2 - t ^ 2) ^ 2 * (s ^ 2 + t ^ 2) *
        (firstShiftedSextic s t) ^ 2)

private abbrev shiftedQuartic (m n : ℤ) : ℤ :=
  m ^ 4 - 6 * m ^ 2 * n ^ 2 + n ^ 4

private abbrev firstDegreeTwelve (m n : ℤ) : ℤ :=
  m ^ 12 - 26 * m ^ 10 * n ^ 2 + 79 * m ^ 8 * n ^ 4
    - 44 * m ^ 6 * n ^ 6 + 79 * m ^ 4 * n ^ 8
    - 26 * m ^ 2 * n ^ 10 + n ^ 12

private abbrev secondDegreeTwelve (m n : ℤ) : ℤ :=
  m ^ 12 - 10 * m ^ 10 * n ^ 2 + 15 * m ^ 8 * n ^ 4
    - 204 * m ^ 6 * n ^ 6 + 15 * m ^ 4 * n ^ 8
    - 10 * m ^ 2 * n ^ 10 + n ^ 12

/-- **Theorem 2, family (3.30)**.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the Integers, Taken Two at a Time, Are Perfect Squares", Theorem 2, family (3.30). -/
theorem_wanted hasSquareElementarySymmetricFunctions_family330_and_entries_square
    (m n : ℤ) :
    let a := (m ^ 4 - n ^ 4) ^ 2 * (shiftedQuartic m n) ^ 2
    let b := 4 * m ^ 2 * n ^ 2 * (m ^ 2 + n ^ 2) ^ 2
      * (shiftedQuartic m n) ^ 2
    let c := 64 * m ^ 4 * n ^ 4 * (m ^ 2 - n ^ 2) ^ 4
    HasSquareElementarySymmetricFunctions a b c ∧
      IsSquare a ∧ IsSquare b ∧ IsSquare c

/-- **Theorem 2, family (3.31)**.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the Integers, Taken Two at a Time, Are Perfect Squares", Theorem 2, family (3.31). -/
theorem_wanted hasSquareElementarySymmetricFunctions_family331_and_entries_square
    (m n : ℤ) :
    let a := 64 * m ^ 4 * n ^ 4 * (m ^ 2 - n ^ 2) ^ 2
    let b := 16 * m ^ 2 * n ^ 2 * (m ^ 2 - n ^ 2) ^ 4
    let c := (m ^ 2 + n ^ 2) ^ 2 * (shiftedQuartic m n) ^ 2
    HasSquareElementarySymmetricFunctions a b c ∧
      IsSquare a ∧ IsSquare b ∧ IsSquare c

/-- **Theorem 2, family (3.32)**.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the Integers, Taken Two at a Time, Are Perfect Squares", Theorem 2, family (3.32). -/
theorem_wanted hasSquareElementarySymmetricFunctions_family332_and_entries_square
    (m n : ℤ) :
    let a := 64 * m ^ 4 * n ^ 4 * (m ^ 2 - n ^ 2) ^ 2
      * (firstDegreeTwelve m n) ^ 2
    let b := (m ^ 2 + n ^ 2) ^ 2 * (shiftedQuartic m n) ^ 2
      * (firstDegreeTwelve m n) ^ 2
    let c := 16 * m ^ 2 * n ^ 2 * (m ^ 2 - n ^ 2) ^ 4
      * (secondDegreeTwelve m n) ^ 2
    HasSquareElementarySymmetricFunctions a b c ∧
      IsSquare a ∧ IsSquare b ∧ IsSquare c

/-- **Theorem 2, family (3.33)**.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the Integers, Taken Two at a Time, Are Perfect Squares", Theorem 2, family (3.33). -/
theorem_wanted hasSquareElementarySymmetricFunctions_family333_and_entries_square
    (m n : ℤ) :
    let a := (m ^ 4 - n ^ 4) ^ 2 * (shiftedQuartic m n) ^ 2
      * (secondDegreeTwelve m n) ^ 2
    let b := 64 * m ^ 4 * n ^ 4 * (m ^ 2 - n ^ 2) ^ 4
      * (secondDegreeTwelve m n) ^ 2
    let c := 4 * m ^ 2 * n ^ 2 * (m ^ 2 + n ^ 2) ^ 2
      * (shiftedQuartic m n) ^ 2 * (firstDegreeTwelve m n) ^ 2
    HasSquareElementarySymmetricFunctions a b c ∧
      IsSquare a ∧ IsSquare b ∧ IsSquare c

private abbrev degreeEightFactor (r s : ℤ) : ℤ :=
  r ^ 8 + 2 * r ^ 6 * s ^ 2 - 12 * r ^ 4 * s ^ 4
    - 6 * r ^ 2 * s ^ 6 - s ^ 8

private abbrev degreeTwelveFactor (r s : ℤ) : ℤ :=
  r ^ 12 + 6 * r ^ 10 * s ^ 2 + 87 * r ^ 8 * s ^ 4
    + 108 * r ^ 6 * s ^ 6 + 55 * r ^ 4 * s ^ 8
    + 14 * r ^ 2 * s ^ 10 + s ^ 12

private abbrev degreeSixFactor (r s : ℤ) : ℤ :=
  5 * r ^ 6 + 3 * r ^ 4 * s ^ 2 + 3 * r ^ 2 * s ^ 4 + s ^ 6

/-- **Theorem 3, family (3.34)**: in the nondegenerate parameter range of
the proof, the entries are sums of two nonzero integer squares and their
symmetric functions are squares.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the Integers, Taken Two at a Time, Are Perfect Squares", Theorem 3, family (3.34). -/
theorem_wanted hasSquareElementarySymmetricFunctions_family334_and_entries_sum_two_nonzero_squares
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) :
    let a := r ^ 2 * (r ^ 2 + s ^ 2) * (degreeEightFactor r s) ^ 2
      * degreeTwelveFactor r s
    let b := s ^ 2 * (r ^ 2 + s ^ 2) * (degreeSixFactor r s) ^ 2
      * (degreeEightFactor r s) ^ 2
    let c := 4 * r ^ 4 * s ^ 4 * (degreeSixFactor r s) ^ 2
      * degreeTwelveFactor r s
    HasSquareElementarySymmetricFunctions a b c ∧
      IsSumTwoNonzeroSquaresℤ a ∧
      IsSumTwoNonzeroSquaresℤ b ∧
      IsSumTwoNonzeroSquaresℤ c

end MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted
