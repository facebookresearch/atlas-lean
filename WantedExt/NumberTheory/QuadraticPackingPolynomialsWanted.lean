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

/-- The integer lattice points `I(α) = S(α) ∩ ℤ²` of the sector
`S(α) = {(x, y) ∈ ℝ² : 0 ≤ y ≤ α x}`, viewed as a subset of `ℝ × ℝ`.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 1 (definition of `S(α)` and `I(α)`). -/
public def sectorLatticePoints (α : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ x y : ℤ, p = ((x : ℝ), (y : ℝ)) ∧ 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ α * x}

/-- The origin lies in every lattice sector `I(α)`.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 1 (definition of `I(α)`). -/
public theorem zero_mem_sectorLatticePoints (α : ℝ) : ((0 : ℝ), (0 : ℝ)) ∈ sectorLatticePoints α :=
  ⟨0, 0, by simp⟩

/-- `P` is a quadratic packing polynomial (QPP) on `S ⊆ ℝ²`: a real polynomial of total
degree two in `x, y` that maps `S` bijectively onto `ℕ₀`.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Definition 1. -/
public def IsQuadraticPackingPolynomial (S : Set (ℝ × ℝ)) (P : ℝ → ℝ → ℝ) : Prop :=
  (∃ a b c d e f : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
      ∀ x y, P x y = a * x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + f) ∧
    Set.BijOn (fun p : ℝ × ℝ => P p.1 p.2) S (Set.range ((↑) : ℕ → ℝ))

/-- A quadratic packing polynomial takes a natural-number value at every point of its set.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Definition 1. -/
public theorem IsQuadraticPackingPolynomial.exists_nat_eq {S : Set (ℝ × ℝ)}
    {P : ℝ → ℝ → ℝ} (hP : IsQuadraticPackingPolynomial S P) {p : ℝ × ℝ} (hp : p ∈ S) :
    ∃ N : ℕ, (N : ℝ) = P p.1 p.2 :=
  hP.2.mapsTo hp

/-- The `i`-th staircase `J_i = {(x, y) ∈ I(n/m) : n x - (m - 1) y = l i}` of the sector of
slope `n / m`, where `l = gcd(m - 1, n)`.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 2 (definition of the staircases `J_i`). -/
public def sectorStaircase (m n i : ℕ) : Set (ℝ × ℝ) :=
  {p | p ∈ sectorLatticePoints ((n : ℝ) / m) ∧
    (n : ℝ) * p.1 - ((m : ℝ) - 1) * p.2 = (Nat.gcd (m - 1) n : ℝ) * i}

/-- The origin lies on the staircase `J_0`.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 2 (definition of the staircases `J_i`). -/
public theorem zero_mem_sectorStaircase_zero (m n : ℕ) :
    ((0 : ℝ), (0 : ℝ)) ∈ sectorStaircase m n 0 :=
  ⟨zero_mem_sectorLatticePoints _, by simp⟩

/-- The height `ȳ_i` of the first step (the point of least `y`-coordinate) of the staircase
`J_i`.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 3 (definition of `ȳ_i`). -/
public noncomputable def staircaseFirstHeight (m n i : ℕ) : ℕ :=
  sInf {y : ℕ | ∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n i}

/-- The first step of `J_0` is the origin: `ȳ_0 = 0`.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 3 (definition of `ȳ_i`). -/
public theorem staircaseFirstHeight_zero (m n : ℕ) : staircaseFirstHeight m n 0 = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inl ⟨0, by simpa using zero_mem_sectorStaircase_zero m n⟩)

/-- The step difference `k = P(x + (m - 1)/l, y + n/l) - P(x, y)` of `P` between consecutive
steps of a staircase of the sector of slope `n / m`, `l = gcd(m - 1, n)`, evaluated at the
base point `(0, 0)`. For every polynomial of the form in Theorem 2 (Stanton) this difference
does not depend on the base point, which is how the paper defines `k`.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 2 (definition of `k`). -/
public noncomputable def consecutiveStepDifference (m n : ℕ) (P : ℝ → ℝ → ℝ) : ℝ :=
  P (((m : ℝ) - 1) / Nat.gcd (m - 1) n) ((n : ℝ) / Nat.gcd (m - 1) n) - P 0 0

/-- The recurring example `P(x, y) = 6 (x - y/2)(x - y/2 - 3/2) + x + y + 2` on `I(12/7)` has
step difference `k = 3`.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Example 10. -/
public theorem consecutiveStepDifference_example_twelve_sevenths :
    consecutiveStepDifference 7 12
      (fun x y => 6 * (x - y / 2) * (x - y / 2 - 3 / 2) + x + y + 2) = 3 := by
  have h : Nat.gcd (7 - 1) 12 = 6 := by norm_num
  simp only [consecutiveStepDifference, h]
  norm_num

/-- Necessary form of a QPP on a sector (Gjaldbæk): if `P` is a QPP on `I(α)`, `α > 0`, then
`P(x, y) = A/2 x(x - 1) + B x y + C/2 y(y - 1) + D x + E y + F` with integers `A, …, F`,
`A > 0`, `B² = A C` and `α = A / (1 - B)`; in particular `α` is rational.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Theorem 1 (`integers-2025-A81-thm-1`). -/
public theorem_wanted quadraticPackingPolynomial_sector_form {α : ℝ} (hα : 0 < α)
    {P : ℝ → ℝ → ℝ} (hP : IsQuadraticPackingPolynomial (sectorLatticePoints α) P) :
    ∃ A B C D E F : ℤ,
      (∀ x y, P x y = (A : ℝ) / 2 * x * (x - 1) + B * x * y + (C : ℝ) / 2 * y * (y - 1) +
        D * x + E * y + F) ∧
      0 < A ∧ B ^ 2 = A * C ∧ α = (A : ℝ) / (1 - B)

/-- Stanton's form of a QPP on a rational sector: if `α = n / m` with `gcd(m, n) = 1` and `P`
is a QPP on `I(n/m)`, then `n ∣ (m - 1)²` and
`P(x, y) = n/2 (x - (m-1)/n y)² + (D - n/2) x + (E - ((m-1)²/n)/2) y + F` with integers
`D, E, F`.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Theorem 2 (`integers-2025-A81-thm-2`). -/
public theorem_wanted quadraticPackingPolynomial_rational_sector_form {m n : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P) :
    (n : ℤ) ∣ ((m : ℤ) - 1) ^ 2 ∧
      ∃ D E F : ℤ, ∀ x y, P x y =
        (n : ℝ) / 2 * (x - ((m : ℝ) - 1) / n * y) ^ 2 + (D - (n : ℝ) / 2) * x +
          (E - (((m : ℝ) - 1) ^ 2 / n) / 2) * y + F

/-- The sheared polynomial `P̂(x, y) = 6x(x - 3/2) + x + 3/2 y + 2` is a QPP on the sheared
lattice sector `Î(12/7) = M(I(12/7))`, `M(x, y) = (x - y/2, y)`.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Example 10 and Figure 3 (`integers-2025-A81-thm-3`). -/
public theorem_wanted isQuadraticPackingPolynomial_sheared_example_twelve_sevenths :
    IsQuadraticPackingPolynomial
      ((fun p : ℝ × ℝ => (p.1 - 1 / 2 * p.2, p.2)) '' sectorLatticePoints ((12 : ℝ) / 7))
      (fun x y => 6 * x * (x - 3 / 2) + x + 3 / 2 * y + 2)

/-- Lemma 11: if `P` is a QPP on `I(n/m)` with step difference `k > 0`, then, with
`l = gcd(m - 1, n)`, `F = P(0, 0)` and `P̂(x, y) = P(x + (m-1)/n y, y)`, one has
`P̂(k/(n/l), ȳ_k) = F + k`, and `P̂(x, y) = n/2 x(x - 1) + D x + k/(n/l) y + F` (Equation (3))
with `D = n/l - (kl - n)/2 - ȳ_k`. The step difference is taken as a natural number; by
Theorem 1 it is an integer for every QPP.

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

/-- Lemma 13: if `P` is a QPP on `I(n/m)` with step difference `k > 0`, then for every `i`
the values of `P` on the staircase `J_{i+k}` lie in the same residue class modulo `k` as its
values on `J_i`.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Lemma 2 (`integers-2025-A81-lem-2`). -/
public theorem_wanted quadraticPackingPolynomial_staircase_congruence {m n k : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P)
    (hk : 0 < k) (hkP : consecutiveStepDifference m n P = k) (i : ℕ) {p q : ℝ × ℝ}
    (hp : p ∈ sectorStaircase m n i) (hq : q ∈ sectorStaircase m n (i + k)) :
    ∃ z : ℤ, P q.1 q.2 - P p.1 p.2 = z * k

/-- Lemma 15: if `P` is a QPP on `I(n/m)` with step difference `k > 0`, then the first step of
the staircase `J_k` has height `ȳ_k = n/l - 1`, `l = gcd(m - 1, n)`.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Lemma 3 (`integers-2025-A81-lem-3`). -/
public theorem_wanted quadraticPackingPolynomial_staircaseFirstHeight {m n k : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P)
    (hk : 0 < k) (hkP : consecutiveStepDifference m n P = k) :
    staircaseFirstHeight m n k = n / Nat.gcd (m - 1) n - 1

/-- Lemma 18 (with the paper's standing assumption `n/l ∣ l` made explicit): let `m, n` be
positive and coprime, `l = gcd(m - 1, n)` with `n/l ∣ l`, `k > 0` with
`k ≡ (m - 1)/l (mod n/l)`, and `P̂(x, y) = n/2 x(x - k/(n/l)) + x + k/(n/l) y + F`. Then `P̂`
is a QPP on `Î(n/m) = M(I(n/m))`, `M(x, y) = (x - (m-1)/n y, y)`, if and only if
`{P̂(i/(n/l), ȳ_i) : 0 ≤ i < k} = {0, 1, …, k - 1}`.

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

/-- Lemma 20: if `P` is a QPP on `I(n/m)` with step difference `k > 0`, then its constant term
is `F = P(0, 0) = (l²/n)(k - 1)(k + 1)/12`, `l = gcd(m - 1, n)`.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Lemma 5 (`integers-2025-A81-lem-5`). -/
public theorem_wanted quadraticPackingPolynomial_constant_term {m n k : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P)
    (hk : 0 < k) (hkP : consecutiveStepDifference m n P = k) :
    P 0 0 = ((Nat.gcd (m - 1) n : ℝ) ^ 2 / n) * (k - 1) * (k + 1) / 12

/-- Proposition 17: if `P` is a QPP on `I(n/m)` with step difference `k > 0` and
`l = gcd(n, m - 1)`, then `n/l ∣ l`, `k ≡ (m - 1)/l (mod n/l)`, and the sheared polynomial
`P̂(x, y) = P(x + (m-1)/n y, y)` equals `n/2 x(x - k/(n/l)) + x + k/(n/l) y + F` with
`F = P(0, 0)` (Equation (8)).

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
