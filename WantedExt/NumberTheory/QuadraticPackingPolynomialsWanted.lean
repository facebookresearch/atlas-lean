/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.ModEq
public import MathlibExt.NumberTheory.QuadraticPackingPolynomials
public import MathlibExt.NumberTheory.QuadraticPackingPolynomialsShearedCriterion

/-!
# Quadratic packing polynomials on sectors of `ℝ²`

Statements from Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on
Sectors of R^2*, INTEGERS 25 (2025), Article A81.

Throughout, the rational sector of slope `n / m` is taken with `m, n` positive and coprime,
the paper's standing convention (Theorem 2). The staircases `J_i`, their first heights
`ȳ_i`, the step difference `k` and the sheared polynomial
`P̂(x, y) = P(x + (m - 1) / n * y, y)` (the paper's `P ∘ M⁻¹`, Section 2) are as in the
paper. A statement about `P̂` on the sheared lattice `Î(n/m) = M(I(n/m))` is stated for `P`
on `I(n/m)`; the two are equivalent because `M` maps `I(n/m)` bijectively onto `Î(n/m)` and
each `J_i` onto `Ĵ_i`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Form of a quadratic packing polynomial on a sector (Gjaldbæk).** Let $\alpha > 0$ be a real
number and let $P$ be a quadratic packing polynomial on the lattice sector $I(\alpha)$. Then there
are integers $A, B, C, D, E, F$ with $A > 0$, $B^2 = AC$ and $\alpha = A/(1 - B)$ such that for
all real $x, y$
$$P(x, y) = \tfrac{A}{2} x(x - 1) + Bxy + \tfrac{C}{2} y(y - 1) + Dx + Ey + F.$$
In particular $\alpha$ is rational.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Theorem 1 (`integers-2025-A81-thm-1`). -/
public theorem_wanted quadraticPackingPolynomial_sector_form {α : ℝ} (hα : 0 < α)
    {P : ℝ → ℝ → ℝ} (hP : IsQuadraticPackingPolynomial (sectorLatticePoints α) P) :
    ∃ A B C D E F : ℤ,
      (∀ x y, P x y = (A : ℝ) / 2 * x * (x - 1) + B * x * y + (C : ℝ) / 2 * y * (y - 1) +
        D * x + E * y + F) ∧
      0 < A ∧ B ^ 2 = A * C ∧ α = (A : ℝ) / (1 - B)

/-- **Stanton's form of a quadratic packing polynomial on a rational sector.** Let $m, n$ be
coprime positive integers and let $P$ be a quadratic packing polynomial on the lattice points
$I(n/m)$ of the sector of slope $n/m$. Then $n$ divides $(m - 1)^2$, and there are integers
$D, E, F$ such that for all real $x, y$
$$
P(x, y) = \frac{n}{2} \left(x - \frac{m - 1}{n} y\right)^2 + \left(D - \frac{n}{2}\right) x +
  \left(E - \frac{(m - 1)^2}{2n}\right) y + F.
$$

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Theorem 2 (`integers-2025-A81-thm-2`). -/
public theorem_wanted quadraticPackingPolynomial_rational_sector_form {m n : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P) :
    (n : ℤ) ∣ ((m : ℤ) - 1) ^ 2 ∧
      ∃ D E F : ℤ, ∀ x y, P x y =
        (n : ℝ) / 2 * (x - ((m : ℝ) - 1) / n * y) ^ 2 + (D - (n : ℝ) / 2) * x +
          (E - (((m : ℝ) - 1) ^ 2 / n) / 2) * y + F

/-- **First step value and sheared form of a quadratic packing polynomial.** Let $m, n$ be
coprime positive integers, let $l = \gcd(m - 1, n)$, and let $P$ be a quadratic packing
polynomial on the lattice points $I(n/m)$ of the sector of slope $n/m$ whose step difference
for $m, n$ is a positive integer $k$. Put $F = P(0, 0)$ and
$\hat P(x, y) = P(x + \frac{m - 1}{n} y, y)$, and let $\bar y_k$ be the height of the first step
of the $k$-th staircase of the sector. Then $\hat P(k/(n/l), \bar y_k) = F + k$, and for all
real $x, y$ one has $\hat P(x, y) = \frac{n}{2} x (x - 1) + D x + \frac{k}{n/l} y + F$ with
$D = n/l - (kl - n)/2 - \bar y_k$.

The step difference is taken as a natural number; by Theorem 1 of the source it is an integer
for every quadratic packing polynomial.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Lemma 1 (`integers-2025-A81-lem-1`). -/
public theorem_wanted quadraticPackingPolynomial_first_step_value {m n k : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P)
    (hk : 0 < k) (hkP : consecutiveStepDifference m n P = k) :
    let l : ℝ := Nat.gcd (m - 1) n
    let Phat : ℝ → ℝ → ℝ := fun x y => P (x + ((m : ℝ) - 1) / n * y) y
    Phat (k / (n / l)) (staircaseFirstHeight m n k) = P 0 0 + k ∧
      ∀ x y, Phat x y = (n : ℝ) / 2 * x * (x - 1) +
        (n / l - (k * l - n) / 2 - staircaseFirstHeight m n k) * x + k / (n / l) * y + P 0 0

/-- **Staircase congruence for quadratic packing polynomials.** Let $m, n$ be positive coprime
integers, let $P$ be a quadratic packing polynomial on the lattice sector $I(n/m)$, and suppose
that the step difference of $P$ equals a positive integer $k$. Then for every natural number
$i$, every point $p$ of the staircase $J_i$ and every point $q$ of the staircase $J_{i+k}$, the
difference $P(q) - P(p)$ is an integer multiple of $k$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Lemma 2 (`integers-2025-A81-lem-2`). -/
public theorem_wanted quadraticPackingPolynomial_staircase_congruence {m n k : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P)
    (hk : 0 < k) (hkP : consecutiveStepDifference m n P = k) (i : ℕ) {p q : ℝ × ℝ}
    (hp : p ∈ sectorStaircase m n i) (hq : q ∈ sectorStaircase m n (i + k)) :
    ∃ z : ℤ, P q.1 q.2 - P p.1 p.2 = z * k

/-- **Height of the first step of the k-th staircase.** Let $m, n$ be positive coprime integers
and $l = \gcd(m - 1, n)$, let $P$ be a quadratic packing polynomial on the lattice sector
$I(n/m)$, and suppose that the step difference of $P$ equals a positive integer $k$. Then the
first height of the staircase $J_k$ is $\bar y_k = n/l - 1$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Lemma 3 (`integers-2025-A81-lem-3`). -/
public theorem_wanted quadraticPackingPolynomial_staircaseFirstHeight {m n k : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P)
    (hk : 0 < k) (hkP : consecutiveStepDifference m n P = k) :
    staircaseFirstHeight m n k = n / Nat.gcd (m - 1) n - 1

/-- **Constant term of a quadratic packing polynomial on a rational sector.** Let $m, n$ be
coprime positive integers, let $l = \gcd(m - 1, n)$, and let $P$ be a quadratic packing
polynomial on the lattice points $I(n/m)$ of the sector of slope $n/m$. If the step difference
of $P$ for $m, n$ is a positive integer $k$, then $P(0, 0) = \frac{l^2}{n} (k - 1)(k + 1)/12$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Lemma 5 (`integers-2025-A81-lem-5`). -/
public theorem_wanted quadraticPackingPolynomial_constant_term {m n k : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P)
    (hk : 0 < k) (hkP : consecutiveStepDifference m n P = k) :
    P 0 0 = ((Nat.gcd (m - 1) n : ℝ) ^ 2 / n) * (k - 1) * (k + 1) / 12

/-- **Step-difference form of a quadratic packing polynomial on a rational sector.** Let $m, n$
be coprime positive integers, let $l = \gcd(m - 1, n)$, and let $P$ be a quadratic packing
polynomial on the lattice points $I(n/m)$ of the sector of slope $n/m$ whose step difference
for $m, n$ is a positive integer $k$. Then $n/l$ divides $l$, $k \equiv (m - 1)/l \pmod{n/l}$,
and for all real $x, y$ one has $P(x + \frac{m - 1}{n} y, y) =
\frac{n}{2} x \left(x - \frac{k}{n/l}\right) + x + \frac{k}{n/l} y + P(0, 0)$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Proposition 1 (`integers-2025-A81-prop-1`). -/
public theorem_wanted quadraticPackingPolynomial_necessary_form {m n k : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P)
    (hk : 0 < k) (hkP : consecutiveStepDifference m n P = k) :
    n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n ∧
      k ≡ (m - 1) / Nat.gcd (m - 1) n [MOD n / Nat.gcd (m - 1) n] ∧
      ∀ x y, P (x + ((m : ℝ) - 1) / n * y) y =
        (n : ℝ) / 2 * x * (x - k / (n / (Nat.gcd (m - 1) n : ℝ))) + x +
          k / (n / (Nat.gcd (m - 1) n : ℝ)) * y + P 0 0

end

end MetaMathlibExt
