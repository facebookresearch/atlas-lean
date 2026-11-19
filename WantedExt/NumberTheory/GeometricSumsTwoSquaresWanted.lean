/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Geometric sums as sums of two squares

Statements from Lorenz Halbeisen, Norbert Hungerbühler,
and Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", *INTEGERS* 26 (2026), Article A30
(<https://math.colgate.edu/~integers/vol26.html>).

A prime is *Pythagorean* if it is `2` or congruent to
`1 (mod 4)`; "is the product of Pythagorean primes" is
stated as: every natural prime divisor is Pythagorean.
The geometric sums are `∑_{j<q} p^{nj}` and their
alternating analogues. In Corollaries 8 and 11 the
number of terms is `q = p^k` while the base stays `p`
(the extraction prints the summand base as `q`, but the
base-`p` reading is the unique one consistent with the
claims, as exact factorizations confirm; e.g. the
base-`q` reading already fails for `p = 3, k = 2, n = 1`).
The sign patterns of `phi4pX1` and `phi4pY1` were pinned
by solving `X_1^2 + Y_1^2 = Φ_{4p}(x)` for small primes.

Proposition 1 is stated from the journal text (its
parity conclusions are truncated in the extraction).
Not stated (see the source audit table): Proposition 12
(a summary paragraph restating Theorem 10 and
Corollary 11, both stated here).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

set_option autoImplicit false

@[expose] public section

open Polynomial

namespace MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted

/-- The even polynomial
`X_1 = x^{p-1} - x^{p-3} + ... - (-1)^{(p-1)/2} x^2 +
(-1)^{(p-1)/2}` of Proposition 2.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Proposition 2. -/
noncomputable def phi4pX1 (p : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range ((p + 1) / 2),
    (-1 : ℤ) ^ i • X ^ (p - 1 - 2 * i)

/-- The odd polynomial
`Y_1 = x^{p-2} - x^{p-4} + ... + (-1)^{(p-1)/2} x^3 -
(-1)^{(p-1)/2} x` of Proposition 2.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Proposition 2. -/
noncomputable def phi4pY1 (p : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range ((p - 1) / 2),
    (-1 : ℤ) ^ i • X ^ (p - 2 - 2 * i)

/-- **Proposition 2**: for each odd prime `p`,
`Φ_{4p}(x) = X_1(x)^2 + Y_1(x)^2` for the explicit
polynomials `X_1` and `Y_1` above.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Proposition 2. -/
theorem_wanted cyclotomicFourMul_eq_sq_add_sq (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    Polynomial.cyclotomic (4 * p) ℤ =
      phi4pX1 p ^ 2 + phi4pY1 p ^ 2

/-- **Corollary 3**: for an odd prime `p` and
`k ≥ 1`, `Φ_{4p^k}(x)` is the sum of the squares of
`X_1` and `Y_1` evaluated at `x^{p^{k-1}}`.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Corollary 3. -/
theorem_wanted cyclotomicFourMulPow_eq_sq_add_sq (p k : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) :
    Polynomial.cyclotomic (4 * p ^ k) ℤ =
      (phi4pX1 p).comp (X ^ (p ^ (k - 1))) ^ 2 +
        (phi4pY1 p).comp (X ^ (p ^ (k - 1))) ^ 2

/-- **Proposition 4**: for each `q ≥ 1`, the
cyclotomic polynomial `Φ_{4q}(x)` is a sum of two
squares in `ℤ[x]` (the paper gives the two squares
explicitly from a product over primitive `4q`-th roots
of unity in the class `1 (mod 4)`).

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Proposition 4. -/
theorem_wanted exists_sq_add_sq_eq_cyclotomic (q : ℕ) (hq : 1 ≤ q) :
    ∃ A B : ℤ[X], Polynomial.cyclotomic (4 * q) ℤ = A ^ 2 + B ^ 2

/-- **Theorem 10**: let `n` be a positive odd integer
and `p ≡ 3 (mod 4)` a prime. Then the geometric sum
`1 + p^n + p^{2n} + ... + p^{(p-1)n}` is the product of
Pythagorean primes, equivalently the sum of two squares.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Theorem 10. -/
theorem_wanted geomSum_pythagorean (p n : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 3) (hn : Odd n) (hn0 : 0 < n) :
    (∀ q : ℕ, q.Prime →
      q ∣ ∑ j ∈ Finset.range p, p ^ (n * j) → q = 2 ∨ q % 4 = 1) ∧
      ∃ a b : ℕ, ∑ j ∈ Finset.range p, p ^ (n * j) = a ^ 2 + b ^ 2

/-- **Corollary 11**: let `p ≡ 3 (mod 4)` be a prime,
`n` a positive odd integer, and `q = p^k` for some
positive integer `k`. Then there are integers `a, b`
with `1 + p^n + p^{2n} + ... + p^{(q-1)n} = a^2 + b^2`.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Corollary 11. -/
theorem_wanted geomSumPow_eq_sq_add_sq (p n k : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 3) (hn : Odd n) (hn0 : 0 < n) (hk : 1 ≤ k) :
    ∃ a b : ℤ, (∑ j ∈ Finset.range (p ^ k), (p : ℤ) ^ (n * j)) =
      a ^ 2 + b ^ 2

/-- **Theorem 5**: let `n` be a positive even integer
and `p` an odd prime. Then the alternating geometric
sum `1 - p^n + p^{2n} - ... + p^{(p-1)n}` is the product
of Pythagorean primes; in fact it is the sum of the
squares of two relatively prime natural numbers.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Theorem 5. -/
theorem_wanted altGeomSum_pythagorean (p n : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : Even n) (hn0 : 0 < n) :
    (∀ q : ℕ, q.Prime →
      (q : ℤ) ∣ ∑ j ∈ Finset.range p, (-1 : ℤ) ^ j * (p : ℤ) ^ (n * j) →
        q = 2 ∨ q % 4 = 1) ∧
      ∃ a b : ℕ, (∑ j ∈ Finset.range p, (-1 : ℤ) ^ j * (p : ℤ) ^ (n * j)) =
        (a : ℤ) ^ 2 + (b : ℤ) ^ 2 ∧ Nat.Coprime a b

/-- **Theorem 7**: let `n` be a natural number and
`p ≡ 1 (mod 4)` a prime. Then the alternating geometric
sum `1 - p^n + p^{2n} - ... + p^{(p-1)n}` is the product
of Pythagorean primes, equivalently the sum of two
squares.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Theorem 7. -/
theorem_wanted altGeomSum_pythagorean_one_mod_four (p n : ℕ)
    (hp : p.Prime) (hp4 : p % 4 = 1) :
    (∀ q : ℕ, q.Prime →
      (q : ℤ) ∣ ∑ j ∈ Finset.range p, (-1 : ℤ) ^ j * (p : ℤ) ^ (n * j) →
        q = 2 ∨ q % 4 = 1) ∧
      ∃ a b : ℕ, (∑ j ∈ Finset.range p, (-1 : ℤ) ^ j * (p : ℤ) ^ (n * j)) =
        (a : ℤ) ^ 2 + (b : ℤ) ^ 2

/-- **Corollary 8**: let `p ≡ 1 (mod 4)` be a prime, `n`
a positive odd integer, and `q = p^k` for some positive
integer `k`. Then there are integers `a, b` with
`1 - p^n + p^{2n} - ... + p^{(q-1)n} = a^2 + b^2`.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Corollary 8. -/
theorem_wanted altGeomSumPow_eq_sq_add_sq (p n k : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) (hn : Odd n) (hn0 : 0 < n) (hk : 1 ≤ k) :
    ∃ a b : ℤ,
      (∑ j ∈ Finset.range (p ^ k), (-1 : ℤ) ^ j * (p : ℤ) ^ (n * j)) =
        a ^ 2 + b ^ 2

/-- **Proposition 9**: for each positive odd integer
`n` and each prime `p ≡ 3 (mod 4)`, there are integers
`a, b` with
`1 - p^n + p^{2n} - ... + p^{(p-1)n} = a^2 - b^2`.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Proposition 9. -/
theorem_wanted altGeomSum_eq_sq_sub_sq (p n : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 3) (hn : Odd n) (hn0 : 0 < n) :
    ∃ a b : ℤ,
      (∑ j ∈ Finset.range p, (-1 : ℤ) ^ j * (p : ℤ) ^ (n * j)) =
        a ^ 2 - b ^ 2

/-- **Theorem 6**: let `x, y` be integers with
`gcd(x, y) = 1` and `n > 0`. Then
`x^{4n} - x^{4n-2} y^2 + ... - x^2 y^{4n-2} + y^{4n}` is
the product of Pythagorean primes, equivalently the sum
of the squares of two relatively prime natural numbers.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Theorem 6. -/
theorem_wanted altBigeom_pythagorean (x y : ℤ) (n : ℕ)
    (hxy : IsCoprime x y) (hn : 0 < n) :
    (∀ q : ℕ, q.Prime →
      (q : ℤ) ∣ ∑ j ∈ Finset.range (2 * n + 1),
        (-1 : ℤ) ^ j * x ^ (4 * n - 2 * j) * y ^ (2 * j) →
        q = 2 ∨ q % 4 = 1) ∧
      ∃ a b : ℕ,
        (∑ j ∈ Finset.range (2 * n + 1),
          (-1 : ℤ) ^ j * x ^ (4 * n - 2 * j) * y ^ (2 * j)) =
          (a : ℤ) ^ 2 + (b : ℤ) ^ 2 ∧ Nat.Coprime a b

/-- **Proposition 1**: for an odd prime `p` there are
`X_j, Y_j ∈ ℚ[x]` with
`Φ_{4p} = X_1^2 + Y_1^2 = X_2^2 + p Y_2^2 = X_3^2 - p Y_3^2`,
where `X_1, Y_1, 2X_2, 2Y_2, 2X_3, 2Y_3 ∈ ℤ[x]`; if
`p ≡ 1 (mod 4)` then `X_2, Y_2 ∈ ℤ[x]`, and if
`p ≡ 3 (mod 4)` then `X_3, Y_3 ∈ ℤ[x]`; `X_1, X_2, X_3`
are even and `Y_1` is odd; for `p ≡ 1 (mod 4)`, `Y_2` is
odd and `Y_3` even, and for `p ≡ 3 (mod 4)`, `Y_2` is even
and `Y_3` odd. "In `ℤ[x]`" means integer coefficients;
`f` is even (odd) when `f(-x) = f(x)` (`= -f(x)`).

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", INTEGERS 26 (2026), Article A30,
Proposition 1. -/
theorem_wanted cyclotomicFourMul_three_quadratic_forms (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ∃ X₁ Y₁ X₂ Y₂ X₃ Y₃ : ℚ[X],
      Polynomial.cyclotomic (4 * p) ℚ = X₁ ^ 2 + Y₁ ^ 2 ∧
      Polynomial.cyclotomic (4 * p) ℚ = X₂ ^ 2 + C (p : ℚ) * Y₂ ^ 2 ∧
      Polynomial.cyclotomic (4 * p) ℚ = X₃ ^ 2 - C (p : ℚ) * Y₃ ^ 2 ∧
      (∀ f ∈ [X₁, Y₁, 2 * X₂, 2 * Y₂, 2 * X₃, 2 * Y₃], ∀ i, ∃ z : ℤ, f.coeff i = z) ∧
      (p % 4 = 1 → ∀ f ∈ [X₂, Y₂], ∀ i, ∃ z : ℤ, f.coeff i = z) ∧
      (p % 4 = 3 → ∀ f ∈ [X₃, Y₃], ∀ i, ∃ z : ℤ, f.coeff i = z) ∧
      (∀ f ∈ [X₁, X₂, X₃], f.comp (-X) = f) ∧ Y₁.comp (-X) = -Y₁ ∧
      (p % 4 = 1 → Y₂.comp (-X) = -Y₂ ∧ Y₃.comp (-X) = Y₃) ∧
      (p % 4 = 3 → Y₂.comp (-X) = Y₂ ∧ Y₃.comp (-X) = -Y₃)

end MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted
