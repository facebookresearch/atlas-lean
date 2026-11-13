/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

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

/-- **Lattice points of a sector.** For a real number $\alpha$, let
$S(\alpha) = \{(x, y) \in \mathbb{R}^2 : 0 \le y \le \alpha x\}$ be the sector of slope
$\alpha$. Its lattice points are $I(\alpha) = S(\alpha) \cap \mathbb{Z}^2$, viewed as a subset
of $\mathbb{R}^2$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 1 (definition of `S(α)` and `I(α)`). -/
public def sectorLatticePoints (α : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ x y : ℤ, p = ((x : ℝ), (y : ℝ)) ∧ 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ α * x}

/-- **The origin is a lattice point of every sector.** For every real number $\alpha$, the
origin $(0, 0)$ lies in the set $I(\alpha)$ of lattice points of the sector of slope $\alpha$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 1 (definition of `I(α)`). -/
public theorem zero_mem_sectorLatticePoints (α : ℝ) : ((0 : ℝ), (0 : ℝ)) ∈ sectorLatticePoints α :=
  ⟨0, 0, by simp⟩

/-- **Quadratic packing polynomial.** A real function $P(x, y)$ of two real variables is a
quadratic packing polynomial (QPP) on a set $S \subseteq \mathbb{R}^2$ if it is a polynomial of
total degree two, that is, $P(x, y) = a x^2 + b x y + c y^2 + d x + e y + f$ for some real
$a, b, c, d, e, f$ with $a, b, c$ not all zero, and $P$ maps $S$ bijectively onto the set
$\mathbb{N}_0 = \{0, 1, 2, \dots\}$ of natural numbers.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Definition 1. -/
public def IsQuadraticPackingPolynomial (S : Set (ℝ × ℝ)) (P : ℝ → ℝ → ℝ) : Prop :=
  (∃ a b c d e f : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
      ∀ x y, P x y = a * x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + f) ∧
    Set.BijOn (fun p : ℝ × ℝ => P p.1 p.2) S (Set.range ((↑) : ℕ → ℝ))

/-- **Quadratic packing polynomials take natural-number values.** If $P$ is a quadratic packing
polynomial on a set $S \subseteq \mathbb{R}^2$, then for every point $(x, y) \in S$ the value
$P(x, y)$ is a natural number.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Definition 1. -/
public theorem IsQuadraticPackingPolynomial.exists_nat_eq {S : Set (ℝ × ℝ)}
    {P : ℝ → ℝ → ℝ} (hP : IsQuadraticPackingPolynomial S P) {p : ℝ × ℝ} (hp : p ∈ S) :
    ∃ N : ℕ, (N : ℝ) = P p.1 p.2 :=
  hP.2.mapsTo hp

/-- **Staircases of a rational sector.** For natural numbers $m, n, i$, let
$l = \gcd(m - 1, n)$. The $i$-th staircase of the sector of slope $n/m$ is
$J_i = \{(x, y) \in I(n/m) : nx - (m - 1)y = li\}$, where $I(n/m)$ is the set of lattice points
of that sector.

If $m = 0$, the slope $n/m$ is read as $0$ and $l$ as $\gcd(0, n) = n$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 2 (definition of the staircases `J_i`). -/
public def sectorStaircase (m n i : ℕ) : Set (ℝ × ℝ) :=
  {p | p ∈ sectorLatticePoints ((n : ℝ) / m) ∧
    (n : ℝ) * p.1 - ((m : ℝ) - 1) * p.2 = (Nat.gcd (m - 1) n : ℝ) * i}

/-- **The origin lies on the zeroth staircase.** For all natural numbers $m, n$, the origin
$(0, 0)$ lies on the staircase $J_0$ of the sector of slope $n/m$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 2 (definition of the staircases `J_i`). -/
public theorem zero_mem_sectorStaircase_zero (m n : ℕ) :
    ((0 : ℝ), (0 : ℝ)) ∈ sectorStaircase m n 0 :=
  ⟨zero_mem_sectorLatticePoints _, by simp⟩

/-- **First height of a staircase.** For natural numbers $m, n, i$, the first height $\bar y_i$
of the staircase $J_i$ of the sector of slope $n/m$ is the least $y$-coordinate of a point of
$J_i$, that is, the height of its first step; it is $0$ if $J_i$ is empty.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 3 (definition of `ȳ_i`). -/
public noncomputable def staircaseFirstHeight (m n i : ℕ) : ℕ :=
  sInf {y : ℕ | ∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n i}

/-- **The zeroth staircase starts at height zero.** For all natural numbers $m, n$, the first
height of the staircase $J_0$ of the sector of slope $n/m$ is $\bar y_0 = 0$; indeed the origin
lies on $J_0$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 3 (definition of `ȳ_i`). -/
public theorem staircaseFirstHeight_zero (m n : ℕ) : staircaseFirstHeight m n 0 = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inl ⟨0, by simpa using zero_mem_sectorStaircase_zero m n⟩)

/-- **Step difference.** For natural numbers $m, n$ and a real function $P(x, y)$ of two real
variables, let $l = \gcd(m \mathbin{\dot-} 1, n)$, where $m \mathbin{\dot-} 1$ is subtraction
truncated at $0$ (so $l = n$ when $m = 0$). The step difference of $P$ for the sector of slope
$n/m$ is $k = P((m - 1)/l, n/l) - P(0, 0)$, with $m - 1$ here the real difference and division
by $l = 0$ read as $0$: the change $P(x + (m - 1)/l, y + n/l) - P(x, y)$ of $P$ between
consecutive steps of a staircase of the sector, evaluated at the base point $(0, 0)$.

For every polynomial of Stanton's form (Theorem 2 of the source) this difference does not
depend on the base point, which is how the source defines $k$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 2 (definition of `k`). -/
public noncomputable def consecutiveStepDifference (m n : ℕ) (P : ℝ → ℝ → ℝ) : ℝ :=
  P (((m : ℝ) - 1) / Nat.gcd (m - 1) n) ((n : ℝ) / Nat.gcd (m - 1) n) - P 0 0

/-- **Step difference of the slope-$12/7$ example.** Let
$P(x, y) = 6(x - y/2)(x - y/2 - 3/2) + x + y + 2$. For $m = 7$ and $n = 12$ (the sector of
slope $12/7$), the step difference of $P$ is $k = 3$: with $l = \gcd(6, 12) = 6$, one has
$P(1, 2) - P(0, 0) = 3$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Example 10. -/
public theorem consecutiveStepDifference_example_twelve_sevenths :
    consecutiveStepDifference 7 12
      (fun x y => 6 * (x - y / 2) * (x - y / 2 - 3 / 2) + x + y + 2) = 3 := by
  have h : Nat.gcd (7 - 1) 12 = 6 := by norm_num
  simp only [consecutiveStepDifference, h]
  norm_num

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

/-- **The slope-$12/7$ example on the sheared sector.** Let $M(x, y) = (x - y/2, y)$ and let
$\hat I(12/7) = M(I(12/7))$ be the image under $M$ of the lattice points $I(12/7)$ of the sector
of slope $12/7$. Then $\hat P(x, y) = 6x(x - 3/2) + x + \frac{3}{2} y + 2$ is a quadratic
packing polynomial on $\hat I(12/7)$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Example 10 and Figure 3 (`integers-2025-A81-thm-3`). -/
public theorem_wanted isQuadraticPackingPolynomial_sheared_example_twelve_sevenths :
    IsQuadraticPackingPolynomial
      ((fun p : ℝ × ℝ => (p.1 - 1 / 2 * p.2, p.2)) '' sectorLatticePoints ((12 : ℝ) / 7))
      (fun x y => 6 * x * (x - 3 / 2) + x + 3 / 2 * y + 2)

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

/-- **Sheared criterion for quadratic packing polynomials.** Let $m, n$ be coprime positive
integers, let $l = \gcd(m - 1, n)$, and assume that $n/l$ divides $l$. Let $k$ be a positive
integer with $k \equiv (m - 1)/l \pmod{n/l}$, let $F$ be a real number, and let
$\hat P(x, y) = \frac{n}{2} x \left(x - \frac{k}{n/l}\right) + x + \frac{k}{n/l} y + F$. Let
$M(x, y) = (x - \frac{m - 1}{n} y, y)$ and let $\hat I(n/m) = M(I(n/m))$ be the image under $M$
of the lattice points $I(n/m)$ of the sector of slope $n/m$. Then $\hat P$ is a quadratic
packing polynomial on $\hat I(n/m)$ if and only if
$\{\hat P(i/(n/l), \bar y_i) : 0 \le i < k\} = \{0, 1, \dots, k - 1\}$, where $\bar y_i$ is the
height of the first step of the $i$-th staircase of the sector of slope $n/m$.

The divisibility $n/l \mid l$ is a standing assumption of the source, made explicit here.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Lemma 4 (`integers-2025-A81-lem-4`). -/
public theorem_wanted isQuadraticPackingPolynomial_sheared_iff {m n k : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n)
    (hk : 0 < k) (hkm : k ≡ (m - 1) / Nat.gcd (m - 1) n [MOD n / Nat.gcd (m - 1) n])
    (F : ℝ) :
    let l : ℝ := Nat.gcd (m - 1) n
    let Phat : ℝ → ℝ → ℝ := fun x y => (n : ℝ) / 2 * x * (x - k / (n / l)) + x + k / (n / l) * y + F
    IsQuadraticPackingPolynomial
        ((fun p : ℝ × ℝ => (p.1 - ((m : ℝ) - 1) / n * p.2, p.2)) ''
          sectorLatticePoints ((n : ℝ) / m)) Phat ↔
      (fun i : ℕ => Phat (i / (n / l)) (staircaseFirstHeight m n i)) '' Set.Iio k =
        ((↑) : ℕ → ℝ) '' Set.Iio k

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
