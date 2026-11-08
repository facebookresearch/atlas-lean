/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On the Diophantine equation `n^x + (5p)^y = z^2`

Statements from Suton Tadee, "On the Diophantine
Equation `n^x + (5p)^y = z^2`", *INTEGERS* 24 (2024),
Article A68
(<https://math.colgate.edu/~integers/vol24.html>).

Equation (1) is `n^x + (5p)^y = z^2` in nonnegative
integers, with `p` an odd prime. All solution
classifications and non-existence claims below were
checked by brute-force search over small ranges; the
extraction's flattened `√` set-builders are read as
`z^2 = n + 1` resp. `z^2 = 5p + 1` side conditions.

Not stated (see the source audit table): Theorem 1
(the special case `u^2 - v^q = 1` of Mihăilescu's
theorem, already covered by
`MathlibExt.NumberTheory.MihailescuWanted.mihailescu`)
and Corollary 2 (false as extracted: its equation
must have been flattened).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PowAddPowEqSqWanted

/-- **Lemma 1**, case `n = 2`: with `y = 0`, Equation
(1) `2^x + 1 = z^2` has the unique nonnegative
integer solution `(x, z) = (3, 3)`.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Lemma 1. -/
theorem_wanted two_pow_add_one_eq_sq (x z : ℕ) :
    2 ^ x + 1 = z ^ 2 ↔ x = 3 ∧ z = 3

/-- **Lemma 1**, case `n ≠ 2`: with `y = 0`,
`(x, 0, z)` solves Equation (1) if and only if
`x = 1` and `z^2 = n + 1`.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Lemma 1. -/
theorem_wanted pow_add_one_eq_sq (n x z : ℕ) (hn : 1 ≤ n)
    (hn2 : n ≠ 2) :
    n ^ x + 1 = z ^ 2 ↔ x = 1 ∧ z ^ 2 = n + 1

/-- **Corollary 1**: if `x = 0`, then `(0, y, z)` is
a nonnegative integer solution of Equation (1) if
and only if `y = 1` and `z^2 = 5p + 1`.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Corollary 1. -/
theorem_wanted one_add_pow_eq_sq (p y z : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    1 + (5 * p) ^ y = z ^ 2 ↔ y = 1 ∧ z ^ 2 = 5 * p + 1

/-- **Lemma 2**: let `n ≡ 2 (mod 5)` or
`n ≡ 3 (mod 5)`. If `y > 0` and Equation (1) has a
nonnegative integer solution, then `x` is even.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Lemma 2. -/
theorem_wanted even_of_pos_exp (n p x y z : ℕ) (hp : p.Prime)
    (hn : n % 5 = 2 ∨ n % 5 = 3) (hy : 0 < y)
    (h : n ^ x + (5 * p) ^ y = z ^ 2) :
    Even x

/-- **Lemma 3**: let `n ≡ 3 (mod 4)` and
`p ≡ 3 (mod 4)`. If Equation (1) has a nonnegative
integer solution, then `x` and `y` have opposite
parity.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Lemma 3. -/
theorem_wanted opposite_parity (n p x y z : ℕ) (hp : p.Prime)
    (hn : n % 4 = 3) (hp4 : p % 4 = 3)
    (h : n ^ x + (5 * p) ^ y = z ^ 2) :
    x % 2 ≠ y % 2

/-- **Theorem 2**: if `n ≡ 1 (mod 4)` and
`p ≡ 1 (mod 4)`, then Equation (1) has no
nonnegative integer solution.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Theorem 2. -/
theorem_wanted no_solution_mod_four_one (n p : ℕ) (hp : p.Prime)
    (hn : n % 4 = 1) (hp4 : p % 4 = 1) :
    ¬ ∃ x y z : ℕ, n ^ x + (5 * p) ^ y = z ^ 2

/-- **Theorem 3**: if `n = 2` and `p ≡ 3 (mod 4)`,
then `(x, y, z)` is a nonnegative integer solution
of Equation (1) if and only if it is `(3, 0, 3)`,
or `(6, 2, 17)` with `p = 3`, or `(0, 1, z)` with
`z^2 = 5p + 1`.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Theorem 3. -/
theorem_wanted two_pow_solutions (p x y z : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 3) :
    2 ^ x + (5 * p) ^ y = z ^ 2 ↔
      (x = 3 ∧ y = 0 ∧ z = 3) ∨
        (p = 3 ∧ x = 6 ∧ y = 2 ∧ z = 17) ∨
        (x = 0 ∧ y = 1 ∧ z ^ 2 = 5 * p + 1)

/-- **Theorem 4**: if `n ≡ 3 (mod 60)` or
`n ≡ 27 (mod 60)`, and `p ≡ 7 (mod 12)` with
`gcd(n, p) = gcd(n, 5p - 1) = 1`, then `(x, y, z)`
is a nonnegative integer solution of Equation (1)
if and only if it is `(0, 1, z)` with `z^2 = 5p + 1`
or `(1, 0, z)` with `z^2 = n + 1`.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Theorem 4. -/
theorem_wanted solutions_mod_sixty (n p x y z : ℕ) (hp : p.Prime)
    (hn : n % 60 = 3 ∨ n % 60 = 27) (hp12 : p % 12 = 7)
    (h1 : Nat.Coprime n p) (h2 : Nat.Coprime n (5 * p - 1)) :
    n ^ x + (5 * p) ^ y = z ^ 2 ↔
      (x = 0 ∧ y = 1 ∧ z ^ 2 = 5 * p + 1) ∨
        (x = 1 ∧ y = 0 ∧ z ^ 2 = n + 1)

/-- **Corollary 3**: the Diophantine equation
`2^x + 15^y = z^2` has exactly three nonnegative
integer solutions, namely `(3, 0, 3)`, `(0, 1, 4)`
and `(6, 2, 17)`.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Corollary 3. -/
theorem_wanted two_pow_add_fifteen_pow (x y z : ℕ) :
    2 ^ x + 15 ^ y = z ^ 2 ↔
      (x = 3 ∧ y = 0 ∧ z = 3) ∨ (x = 0 ∧ y = 1 ∧ z = 4) ∨
        (x = 6 ∧ y = 2 ∧ z = 17)

/-- **Corollary 4**: the Diophantine equation
`3^x + 35^y = z^2` has only two nonnegative integer
solutions, namely `(1, 0, 2)` and `(0, 1, 6)`.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Corollary 4. -/
theorem_wanted three_pow_add_thirtyfive_pow (x y z : ℕ) :
    3 ^ x + 35 ^ y = z ^ 2 ↔
      (x = 1 ∧ y = 0 ∧ z = 2) ∨ (x = 0 ∧ y = 1 ∧ z = 6)

end MathlibExt.NumberTheory.PowAddPowEqSqWanted
