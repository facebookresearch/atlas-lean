/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Primitive Pythagorean triangles with sides of certain forms

Statements from Yangcheng Li and Yong Zhang, "Primitive Pythagorean
Triangles with Sides of Certain Forms", *INTEGERS* 24 (2024), Article
A31 (<https://math.colgate.edu/~integers/y31/y31.pdf>).

Ordered triples `(X, Y, Z)` have legs `X, Y` and hypotenuse `Z`. For an
integer Pythagorean triple, `Nat.Coprime X Y` is the primitivity
condition used here. Theorem 3 is split into its reciprocal-sum and
reciprocal-difference claims.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Card

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PrimitivePythagoreanFormsWanted

/-- Li and Zhang's Theorem 1: infinitely many primitive Pythagorean
triples have all three sides equal to a sum of two positive squares.

Source: Yangcheng Li and Yong Zhang, "Primitive Pythagorean Triangles
with Sides of Certain Forms", Theorem 1. -/
theorem_wanted primitive_pythagorean_sides_sum_two_squares_infinite :
    Set.Infinite
      {(X, Y, Z) : ℕ × ℕ × ℕ |
        X ^ 2 + Y ^ 2 = Z ^ 2 ∧ Nat.Coprime X Y ∧
          ∃ x y p q r s : ℕ,
            0 < x ∧ 0 < y ∧ 0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧
              X = x ^ 2 + y ^ 2 ∧ Y = p ^ 2 + q ^ 2 ∧
                Z = r ^ 2 + s ^ 2}

/-- Li and Zhang's Corollary 1: infinitely many primitive Pythagorean
triples have first and third sides equal to sums of two positive squares
and middle side equal to one positive square.

Source: Yangcheng Li and Yong Zhang, "Primitive Pythagorean Triangles
with Sides of Certain Forms", Corollary 1. -/
theorem_wanted primitive_pythagorean_sides_square_middle_infinite :
    Set.Infinite
      {(X, Y, Z) : ℕ × ℕ × ℕ |
        X ^ 2 + Y ^ 2 = Z ^ 2 ∧ Nat.Coprime X Y ∧
          ∃ x y p r s : ℕ,
            0 < x ∧ 0 < y ∧ 0 < p ∧ 0 < r ∧ 0 < s ∧
              X = x ^ 2 + y ^ 2 ∧ Y = p ^ 2 ∧ Z = r ^ 2 + s ^ 2}

/-- Li and Zhang's Theorem 2: infinitely many primitive Pythagorean
triples have all three sides equal to a sum of two positive cubes.

Source: Yangcheng Li and Yong Zhang, "Primitive Pythagorean Triangles
with Sides of Certain Forms", Theorem 2. -/
theorem_wanted primitive_pythagorean_sides_sum_two_cubes_infinite :
    Set.Infinite
      {(X, Y, Z) : ℕ × ℕ × ℕ |
        X ^ 2 + Y ^ 2 = Z ^ 2 ∧ Nat.Coprime X Y ∧
          ∃ x y p q r s : ℕ,
            0 < x ∧ 0 < y ∧ 0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧
              X = x ^ 3 + y ^ 3 ∧ Y = p ^ 3 + q ^ 3 ∧
                Z = r ^ 3 + s ^ 3}

/-- The reciprocal-sum part of Li and Zhang's Theorem 3: infinitely many
positive rational right-triangle side triples have each side equal to a
sum of reciprocals of two positive integers.

Source: Yangcheng Li and Yong Zhang, "Primitive Pythagorean Triangles
with Sides of Certain Forms", Theorem 3. -/
theorem_wanted rational_right_triangles_reciprocal_sums_infinite :
    Set.Infinite
      {(X, Y, Z) : ℚ × ℚ × ℚ |
        0 < X ∧ 0 < Y ∧ 0 < Z ∧ X ^ 2 + Y ^ 2 = Z ^ 2 ∧
          ∃ x y p q r s : ℕ,
            0 < x ∧ 0 < y ∧ 0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧
              X = 1 / (x : ℚ) + 1 / (y : ℚ) ∧
                Y = 1 / (p : ℚ) + 1 / (q : ℚ) ∧
                  Z = 1 / (r : ℚ) + 1 / (s : ℚ)}

/-- The reciprocal-difference part of Li and Zhang's Theorem 3:
infinitely many positive rational right-triangle side triples have each
side equal to a difference of reciprocals of two positive integers.

Source: Yangcheng Li and Yong Zhang, "Primitive Pythagorean Triangles
with Sides of Certain Forms", Theorem 3. -/
theorem_wanted rational_right_triangles_reciprocal_differences_infinite :
    Set.Infinite
      {(X, Y, Z) : ℚ × ℚ × ℚ |
        0 < X ∧ 0 < Y ∧ 0 < Z ∧ X ^ 2 + Y ^ 2 = Z ^ 2 ∧
          ∃ x y p q r s : ℕ,
            0 < x ∧ 0 < y ∧ 0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧
              X = 1 / (x : ℚ) - 1 / (y : ℚ) ∧
                Y = 1 / (p : ℚ) - 1 / (q : ℚ) ∧
                  Z = 1 / (r : ℚ) - 1 / (s : ℚ)}

end MathlibExt.NumberTheory.PrimitivePythagoreanFormsWanted
