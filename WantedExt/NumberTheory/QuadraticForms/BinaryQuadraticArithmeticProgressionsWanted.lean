/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Arithmetic progressions represented by binary quadratic forms

Statements from Ajai Choudhry, "Arithmetic Progressions
Represented by Binary Quadratic Forms", *INTEGERS* 25 (2025),
Article A14 (<https://math.colgate.edu/~integers/z14/z14.pdf>).

Irreducibility of an integral binary quadratic form is used in
the paper's sense that its discriminant is not a perfect square.

Proved in
`MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressions`,
which this module imports: the common-denominator scaling
(`exists_int_representations_of_rat_arithmetic_progression`) and
the nine-term progression represented by `p x ^ 2 + q y ^ 2`
(`exists_representation_nine_term_diagonal_quadratic`).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.Basic
public import MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressions

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressionsWanted

/-- **Binary quadratic forms with non-square discriminant represent nine-term progressions.**
Let $a, b, c$ be integers such that the discriminant $b^2 - 4ac$ is not a perfect square. Then
there are integers $u_0$ and $d \ne 0$ such that for every natural number $i < 9$ there are
integers $x, y$ with $u_0 + id = ax^2 + bxy + cy^2$.

The condition $d \ne 0$ excludes constant progressions.

Source: Ajai Choudhry, "Arithmetic Progressions Represented by
Binary Quadratic Forms", Theorem 2. -/
theorem_wanted exists_nine_term_arithmetic_progression_binary_quadratic
    (a b c : ℤ) (hirr : ¬IsSquare (b ^ 2 - 4 * a * c)) :
    ∃ u0 d : ℤ, d ≠ 0 ∧ ∀ i : ℕ, i < 9 → ∃ x y : ℤ,
      u0 + i * d = a * x ^ 2 + b * x * y + c * y ^ 2

end MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressionsWanted
