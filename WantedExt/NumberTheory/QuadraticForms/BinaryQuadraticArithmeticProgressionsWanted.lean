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
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.QuadraticForms.BinaryQuadraticArithmeticProgressionsWanted

/-- **Rational representations of an arithmetic progression scale to integral ones.** Let
$a, b, c$ be integers, $n$ a natural number and $u_0, d$ rational numbers. If for every natural
number $i < n$ there are rational numbers $x, y$ with $ax^2 + bxy + cy^2 = u_0 + id$, then there
is a nonzero integer $k$ such that for every natural number $i < n$ there are integers $x, y$
with $ax^2 + bxy + cy^2 = k^2(u_0 + id)$.

The nonzero condition on $k$ is the paper's common-denominator choice; it also excludes the
trivial zero scaling.

Source: Ajai Choudhry, "Arithmetic Progressions Represented by
Binary Quadratic Forms", Lemma 1. -/
theorem_wanted exists_int_representations_of_rat_arithmetic_progression
    (a b c : ℤ) (n : ℕ) (u0 d : ℚ)
    (hrep : ∀ i ∈ Finset.range n, ∃ x y : ℚ,
      (a : ℚ) * x ^ 2 + (b : ℚ) * x * y + (c : ℚ) * y ^ 2 =
        u0 + i * d) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ i ∈ Finset.range n, ∃ x y : ℤ,
      (a * x ^ 2 + b * x * y + c * y ^ 2 : ℚ) =
        (k : ℚ) ^ 2 * (u0 + i * d)

/-- **Nine-term arithmetic progressions represented by $px^2 + qy^2$.** Let $p, q, g, h$ be
integers such that $-4pq$ is not a perfect square, and put

$$
u_1 = 4p^5g^{10} - 47p^4qg^8h^2 - 156p^3q^2g^6h^4 + 2052p^2q^3g^4h^6 +
4833pq^4g^2h^8 + 324q^5h^{10}
$$

and

$$
d = 12pqg^2h^2(pg^2 - 3qh^2)(pg^2 + 6qh^2)(2pg^2 + 3qh^2).
$$

Then for every natural number $i < 9$ there are integers $x, y$ with $u_1 + id = px^2 + qy^2$.

Source: Ajai Choudhry, "Arithmetic Progressions Represented by
Binary Quadratic Forms", Theorem 1, relations (3.1). -/
theorem_wanted exists_representation_nine_term_diagonal_quadratic
    (p q g h : ℤ) (hirr : ¬IsSquare (-4 * p * q)) :
    ∀ i : ℕ, i < 9 → ∃ x y : ℤ,
      (4 * p ^ 5 * g ^ 10 - 47 * p ^ 4 * q * g ^ 8 * h ^ 2 -
          156 * p ^ 3 * q ^ 2 * g ^ 6 * h ^ 4 +
          2052 * p ^ 2 * q ^ 3 * g ^ 4 * h ^ 6 +
          4833 * p * q ^ 4 * g ^ 2 * h ^ 8 + 324 * q ^ 5 * h ^ 10) +
        i * (12 * p * q * g ^ 2 * h ^ 2 *
          (p * g ^ 2 - 3 * q * h ^ 2) * (p * g ^ 2 + 6 * q * h ^ 2) *
          (2 * p * g ^ 2 + 3 * q * h ^ 2)) =
        p * x ^ 2 + q * y ^ 2

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
