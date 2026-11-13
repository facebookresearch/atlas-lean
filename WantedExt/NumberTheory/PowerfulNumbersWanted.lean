/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Three consecutive powerful numbers of middle-cube form

Statements from Tsz Ho Chan, "A Note on Three Consecutive Powerful
Numbers", *INTEGERS* 25 (2025), Paper A7, DOI 10.5281/zenodo.14679327
(<https://math.colgate.edu/~integers/z7/z7.pdf>).

All variables are integers unless positivity is stated explicitly.
The paper's exact-divisibility notation `3 ∥ N` is spelled out as
`3 ∣ N ∧ ¬ 9 ∣ N`.

Lemma 4 is encoded with a nonzero `X` in the resulting elliptic-curve
solution.  This is the conclusion produced by the paper's proof
(`X = a*x^2 ≠ 0`) and used later in the paper; without it, `(0, 0)`
would trivialize the displayed curve for every `a`, `c`, and `e`.

The Pell generations in Lemmas 5 and 6 use Mathlib's quadratic
integers `ℤ√3`.  Lemma 6 is indexed from the seed `(1, 1)`:
the displayed initial values are the coordinates at exponents `0`
and `1` in `(1 + √3)(2 + √3)^k`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.Zsqrtd.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PowerfulNumbersWanted

/-- **Lemma 1**: the difference of two integer squares is never `2`.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Lemma 1. -/
theorem_wanted int_sq_sub_int_sq_ne_two
    (a b : ℤ) :
    a ^ 2 - b ^ 2 ≠ 2

/-- **Lemma 2**: if `x ≡ 1 (mod 3)`, then `3` exactly divides
`x^2 + x + 1`, in the sense `3 ∣ x^2 + x + 1` but
`¬ 9 ∣ x^2 + x + 1`.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Lemma 2. -/
theorem_wanted three_exact_dvd_sq_add_self_add_one
    (x : ℤ) (hx : x % 3 = 1) :
    3 ∣ x ^ 2 + x + 1 ∧ ¬ 9 ∣ x ^ 2 + x + 1

/-- **Lemma 3**: if `x ≡ 2 (mod 3)`, then `3` exactly divides
`x^2 - x + 1`, in the sense `3 ∣ x^2 - x + 1` but
`¬ 9 ∣ x^2 - x + 1`.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Lemma 3. -/
theorem_wanted three_exact_dvd_sq_sub_self_add_one
    (x : ℤ) (hx : x % 3 = 2) :
    3 ∣ x ^ 2 - x + 1 ∧ ¬ 9 ∣ x ^ 2 - x + 1

/-- **Lemma 4**: a nonzero-`x` integer point on
`y^2 = a*x^4 + c*x^2 + e` yields an integer point with nonzero
`X`-coordinate on `Y^2 = X^3 + c*X^2 + a*e*X`.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Lemma 4. -/
theorem_wanted exists_int_point_elliptic_of_exists_int_point_quartic
    (a c e : ℤ) (ha : a ≠ 0)
    (h : ∃ x y : ℤ, x ≠ 0 ∧ y ^ 2 = a * x ^ 4 + c * x ^ 2 + e) :
    ∃ X Y : ℤ, X ≠ 0 ∧ Y ^ 2 = X ^ 3 + c * X ^ 2 + a * e * X

/-- **Lemma 5**: the positive integer solutions of
`x^2 - 3*y^2 = 1` are exactly the coordinates of
`(2 + √3)^k` for `k ≥ 1`.  The coordinates begin
`(x₁, y₁) = (2, 1)` and `(x₂, y₂) = (7, 4)` and satisfy the
second-order recursion `uₖ₊₂ = 4*uₖ₊₁ - uₖ`.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Lemma 5. -/
theorem_wanted pell_three_eq_one_positive_solutions_iff_and_recurrence :
    (∀ x y : ℤ,
      (0 < x ∧ 0 < y ∧ x ^ 2 - 3 * y ^ 2 = 1) ↔
        ∃ k : ℕ, 1 ≤ k ∧
          (⟨x, y⟩ : ℤ√3) = (⟨2, 1⟩ : ℤ√3) ^ k) ∧
      (((⟨2, 1⟩ : ℤ√3) ^ 1).re = 2 ∧ ((⟨2, 1⟩ : ℤ√3) ^ 1).im = 1 ∧
        ((⟨2, 1⟩ : ℤ√3) ^ 2).re = 7 ∧ ((⟨2, 1⟩ : ℤ√3) ^ 2).im = 4 ∧
        ∀ k : ℕ,
          ((⟨2, 1⟩ : ℤ√3) ^ (k + 2)).re =
              4 * ((⟨2, 1⟩ : ℤ√3) ^ (k + 1)).re -
                ((⟨2, 1⟩ : ℤ√3) ^ k).re ∧
            ((⟨2, 1⟩ : ℤ√3) ^ (k + 2)).im =
              4 * ((⟨2, 1⟩ : ℤ√3) ^ (k + 1)).im -
                ((⟨2, 1⟩ : ℤ√3) ^ k).im)

/-- **Lemma 6**: the positive integer solutions of
`x^2 - 3*y^2 = -2` are exactly the coordinates of
`(1 + √3)(2 + √3)^k` for `k ≥ 0`.  In this zero-based indexing,
the first two coordinate pairs are `(1, 1)` and `(5, 3)`, and both
coordinates satisfy `uₖ₊₂ = 4*uₖ₊₁ - uₖ`.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Lemma 6. -/
theorem_wanted pell_three_eq_neg_two_positive_solutions_iff_and_recurrence :
    (∀ x y : ℤ,
      (0 < x ∧ 0 < y ∧ x ^ 2 - 3 * y ^ 2 = -2) ↔
        ∃ k : ℕ,
          (⟨x, y⟩ : ℤ√3) = (⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ k) ∧
      ((((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ 0).re = 1 ∧
          ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ 0).im = 1 ∧
          ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ 1).re = 5 ∧
          ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ 1).im = 3) ∧
        ∀ k : ℕ,
          ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ (k + 2)).re =
              4 * ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ (k + 1)).re -
                ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ k).re ∧
            ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ (k + 2)).im =
              4 * ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ (k + 1)).im -
                ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ k).im)

/-- **Theorem 1**: there are no primes `p, q` and positive integers
`x, y, z` with `x^3 - 1 = p^3*y^2` and `x^3 + 1 = q^3*z^2`.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Theorem 1. -/
theorem_wanted not_exists_prime_cube_square_neighbors_of_cube :
    ¬ ∃ p q x y z : ℕ,
      p.Prime ∧ q.Prime ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
        (x : ℤ) ^ 3 - 1 = (p : ℤ) ^ 3 * (y : ℤ) ^ 2 ∧
          (x : ℤ) ^ 3 + 1 = (q : ℤ) ^ 3 * (z : ℤ) ^ 2

/-- **Corollary 1**: the equation
`64*x^6 - 1 = p^3*q^3*y^2` has no solution with integers `x, y`
and primes `p, q`.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Corollary 1. -/
theorem_wanted not_exists_sixty_four_mul_pow_six_sub_one_eq :
    ¬ ∃ (p q : ℕ) (x y : ℤ),
      p.Prime ∧ q.Prime ∧
        64 * x ^ 6 - 1 = (p : ℤ) ^ 3 * (q : ℤ) ^ 3 * y ^ 2

end MathlibExt.NumberTheory.PowerfulNumbersWanted
