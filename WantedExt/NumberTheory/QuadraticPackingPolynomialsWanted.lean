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
public import MathlibExt.NumberTheory.QuadraticPackingPolynomialsStaircaseCongruence
public import MathlibExt.NumberTheory.QuadraticPackingPolynomialRationalForm

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

end

end MetaMathlibExt
