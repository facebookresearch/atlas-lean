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

Not stated (see the source audit table): Proposition 1
(its parity conclusions are truncated in the
extraction) and Proposition 12 (a summary paragraph,
not a statement).
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

/-- **The alternating polynomial $X_1$.** For a natural number $p$, $X_1$ is the polynomial with
integer coefficients
$$
X_1(x) = \sum_{i=0}^{\lfloor (p+1)/2 \rfloor - 1} (-1)^i x^{p-1-2i}.
$$
For odd $p \ge 5$ this is the even polynomial
$x^{p-1} - x^{p-3} + \dots - (-1)^{(p-1)/2} x^2 + (-1)^{(p-1)/2}$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Proposition 2. -/
noncomputable def phi4pX1 (p : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range ((p + 1) / 2),
    (-1 : ℤ) ^ i • X ^ (p - 1 - 2 * i)

/-- **The alternating polynomial $Y_1$.** For a natural number $p$, $Y_1$ is the polynomial with
integer coefficients
$$
Y_1(x) = \sum_{i=0}^{\lfloor (p-1)/2 \rfloor - 1} (-1)^i x^{p-2-2i}.
$$
For odd $p \ge 5$ this is the odd polynomial
$x^{p-2} - x^{p-4} + \dots + (-1)^{(p-1)/2} x^3 - (-1)^{(p-1)/2} x$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Proposition 2. -/
noncomputable def phi4pY1 (p : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range ((p - 1) / 2),
    (-1 : ℤ) ^ i • X ^ (p - 2 - 2 * i)

/-- **The cyclotomic polynomial $\Phi_{4p}$ as a sum of two explicit squares.** Let $p$ be an
odd prime, let $X_1 = \sum_{i=0}^{(p-1)/2} (-1)^i x^{p-1-2i}$ and
$Y_1 = \sum_{i=0}^{(p-3)/2} (-1)^i x^{p-2-2i}$ in $\mathbb{Z}[x]$, and let $\Phi_{4p}$ be the
$4p$-th cyclotomic polynomial over $\mathbb{Z}$. Then $\Phi_{4p} = X_1^2 + Y_1^2$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Proposition 2. -/
theorem_wanted cyclotomicFourMul_eq_sq_add_sq (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    Polynomial.cyclotomic (4 * p) ℤ =
      phi4pX1 p ^ 2 + phi4pY1 p ^ 2

/-- **The cyclotomic polynomial $\Phi_{4p^k}$ as a sum of two explicit squares.** Let $p$ be an
odd prime, let $k \ge 1$, let $X_1 = \sum_{i=0}^{(p-1)/2} (-1)^i x^{p-1-2i}$ and
$Y_1 = \sum_{i=0}^{(p-3)/2} (-1)^i x^{p-2-2i}$ in $\mathbb{Z}[x]$, and let $\Phi_{4p^k}$ be the
$4p^k$-th cyclotomic polynomial over $\mathbb{Z}$. Then
$\Phi_{4p^k}(x) = X_1\bigl(x^{p^{k-1}}\bigr)^2 + Y_1\bigl(x^{p^{k-1}}\bigr)^2$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Corollary 3. -/
theorem_wanted cyclotomicFourMulPow_eq_sq_add_sq (p k : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) :
    Polynomial.cyclotomic (4 * p ^ k) ℤ =
      (phi4pX1 p).comp (X ^ (p ^ (k - 1))) ^ 2 +
        (phi4pY1 p).comp (X ^ (p ^ (k - 1))) ^ 2

/-- **Every cyclotomic polynomial $\Phi_{4q}$ is a sum of two squares.** For every integer
$q \ge 1$ there are polynomials $A, B \in \mathbb{Z}[x]$ such that the $4q$-th cyclotomic
polynomial $\Phi_{4q}$ over $\mathbb{Z}$ satisfies $\Phi_{4q} = A^2 + B^2$.

The paper gives the two squares explicitly, from a product over the primitive $4q$-th roots of
unity in the class $1 \pmod 4$; only their existence is stated here.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Proposition 4. -/
theorem_wanted exists_sq_add_sq_eq_cyclotomic (q : ℕ) (hq : 1 ≤ q) :
    ∃ A B : ℤ[X], Polynomial.cyclotomic (4 * q) ℤ = A ^ 2 + B ^ 2

/-- **Geometric sums for primes $p \equiv 3 \pmod 4$ and odd $n$ are sums of two squares.**
Let $p$ be a prime with $p \equiv 3 \pmod 4$, let $n$ be a positive odd integer, and let
$S = \sum_{j=0}^{p-1} p^{nj} = 1 + p^n + p^{2n} + \cdots + p^{(p-1)n}$. Then every prime divisor
of $S$ is $2$ or congruent to $1$ modulo $4$, and there are natural numbers $a, b$ with
$S = a^2 + b^2$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Theorem 10. -/
theorem_wanted geomSum_pythagorean (p n : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 3) (hn : Odd n) (hn0 : 0 < n) :
    (∀ q : ℕ, q.Prime →
      q ∣ ∑ j ∈ Finset.range p, p ^ (n * j) → q = 2 ∨ q % 4 = 1) ∧
      ∃ a b : ℕ, ∑ j ∈ Finset.range p, p ^ (n * j) = a ^ 2 + b ^ 2

/-- **Geometric sums with $p^k$ terms, $p \equiv 3 \pmod 4$ and $n$ odd, are sums of two squares.**
Let $p$ be a prime with $p \equiv 3 \pmod 4$, let $n$ be a positive odd integer, let $k$ be a
positive integer, and put $q = p^k$. Then there are integers $a, b$ with
$\sum_{j=0}^{q-1} p^{nj} = 1 + p^n + p^{2n} + \cdots + p^{(q-1)n} = a^2 + b^2$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Corollary 11. -/
theorem_wanted geomSumPow_eq_sq_add_sq (p n k : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 3) (hn : Odd n) (hn0 : 0 < n) (hk : 1 ≤ k) :
    ∃ a b : ℤ, (∑ j ∈ Finset.range (p ^ k), (p : ℤ) ^ (n * j)) =
      a ^ 2 + b ^ 2

/-- **Alternating geometric sums for odd primes $p$ and even $n$ are sums of two coprime squares.**
Let $p$ be an odd prime, let $n$ be a positive even integer, and let
$S = \sum_{j=0}^{p-1} (-1)^j p^{nj} = 1 - p^n + p^{2n} - \cdots + p^{(p-1)n}$. Then every prime
divisor of $S$ is $2$ or congruent to $1$ modulo $4$, and there are coprime natural numbers
$a, b$ with $S = a^2 + b^2$.

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

/-- **Alternating geometric sums for primes $p \equiv 1 \pmod 4$ are sums of two squares.**
Let $p$ be a prime with $p \equiv 1 \pmod 4$, let $n \ge 0$ be an integer, and let
$S = \sum_{j=0}^{p-1} (-1)^j p^{nj} = 1 - p^n + p^{2n} - \cdots + p^{(p-1)n}$. Then every prime
divisor of $S$ is $2$ or congruent to $1$ modulo $4$, and there are natural numbers $a, b$ with
$S = a^2 + b^2$.

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

/-- **Alternating geometric sums with $p^k$ terms, $p \equiv 1 \pmod 4$, as sums of two squares.**
Let $p$ be a prime with $p \equiv 1 \pmod 4$, let $n$ be a positive odd integer, let $k$ be a
positive integer, and put $q = p^k$. Then there are integers $a, b$ with
$\sum_{j=0}^{q-1} (-1)^j p^{nj} = 1 - p^n + p^{2n} - \cdots + p^{(q-1)n} = a^2 + b^2$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Corollary 8. -/
theorem_wanted altGeomSumPow_eq_sq_add_sq (p n k : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) (hn : Odd n) (hn0 : 0 < n) (hk : 1 ≤ k) :
    ∃ a b : ℤ,
      (∑ j ∈ Finset.range (p ^ k), (-1 : ℤ) ^ j * (p : ℤ) ^ (n * j)) =
        a ^ 2 + b ^ 2

/-- **Alternating geometric sums for primes $p \equiv 3 \pmod 4$ and odd $n$ are differences of
two squares.** Let $p$ be a prime with $p \equiv 3 \pmod 4$ and let $n$ be a positive odd integer.
Then there are integers $a, b$ with
$\sum_{j=0}^{p-1} (-1)^j p^{nj} = 1 - p^n + p^{2n} - \cdots + p^{(p-1)n} = a^2 - b^2$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Proposition 9. -/
theorem_wanted altGeomSum_eq_sq_sub_sq (p n : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 3) (hn : Odd n) (hn0 : 0 < n) :
    ∃ a b : ℤ,
      (∑ j ∈ Finset.range p, (-1 : ℤ) ^ j * (p : ℤ) ^ (n * j)) =
        a ^ 2 - b ^ 2

/-- **An alternating sum in coprime integers $x, y$ is a sum of two coprime squares.**
Let $x$ and $y$ be coprime integers, let $n$ be a positive integer, and let
$S = \sum_{j=0}^{2n} (-1)^j x^{4n-2j} y^{2j}$, that is,
$S = x^{4n} - x^{4n-2} y^2 + \cdots - x^2 y^{4n-2} + y^{4n}$. Then every prime divisor of $S$ is
$2$ or congruent to $1$ modulo $4$, and there are coprime natural numbers $a, b$ with
$S = a^2 + b^2$.

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

end MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted
