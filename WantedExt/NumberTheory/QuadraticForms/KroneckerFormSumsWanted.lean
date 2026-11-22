/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import MathlibExt.NumberTheory.QuadraticForms.Reduced
public import MathlibExt.NumberTheory.QuadraticForms.ThreeSquares

namespace MetaMathlibExt

@[expose] public section

/-- Gauss reducedness of `a * x ^ 2 + b * x * y + c * y ^ 2` is decidable: it is a
conjunction of integer comparisons.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1
(reduced forms `-a < b ≤ a < c` or `0 ≤ b ≤ a = c`, which is
`BinaryQuadraticForm.IsGaussReduced` together with positive definiteness). The instance is
local to this file, so importing it does not change instance search elsewhere. -/
public local instance decidableIsGaussReduced (a b c : ℤ) :
    Decidable (BinaryQuadraticForm.IsGaussReduced a b c) :=
  inferInstanceAs (Decidable (0 < a ∧ discrim a b c < 0 ∧ |b| ≤ a ∧ a ≤ c ∧
    ((|b| = a ∨ a = c) → 0 ≤ b)))

/-- The finite set `R(d)` of reduced positive-definite integral binary quadratic forms
`a * x ^ 2 + b * x * y + c * y ^ 2` (as coefficient triples `(a, b, c)`) of
discriminant `b ^ 2 - 4 * a * c = d`. A reduced form has `|b| ≤ a ≤ c`, so
`-d = 4ac - b² ≥ 3a²` and `a ≤ √(-d)`; given `a` and `b`, the only candidate is
`c = (b² - d) / (4a)`. The search therefore runs over `1 ≤ a ≤ ⌊√(-d)⌋`, `|b| ≤ a` (about
`-d` candidates) and keeps the reduced triples of discriminant `d`; for `d ≥ 0` the set is
empty.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1. -/
public def reducedFormsOfDiscriminant (d : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc (1 : ℤ) (Nat.sqrt (-d).toNat)).biUnion fun a =>
      (Finset.Icc (-a) a).image fun b => (a, b, (b ^ 2 - d) / (4 * a))).filter fun q =>
    BinaryQuadraticForm.IsGaussReduced q.1 q.2.1 q.2.2 ∧ discrim q.1 q.2.1 q.2.2 = d

/-- The Gauss class number `h(d)`: the number of primitive (`gcd(a, b, c) = 1`) reduced
positive-definite forms of discriminant `d`.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1. -/
public def gaussClassNumber (d : ℤ) : ℕ :=
  ((reducedFormsOfDiscriminant d).filter fun q =>
    Int.gcd (Int.gcd q.1 q.2.1 : ℤ) q.2.2 = 1).card

/-- The unweighted Hurwitz class number `H(d)` of the paper, equation (1): the number of
all (not necessarily primitive) reduced positive-definite forms of discriminant `d`.
This differs from the weighted `Nat.hurwitzClassNumber` (the paper remarks that the
literature uses several conventions).

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, equation (1). -/
public def unweightedHurwitzClassNumber (d : ℤ) : ℕ :=
  (reducedFormsOfDiscriminant d).card

/-- The weight of a reduced form, equation (3): `1 / 2` if `a = c` and `b = 0`, `1 / 3`
if `a = b = c`, and `1` otherwise.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, equation (3). -/
public def reducedFormWeight (q : ℤ × ℤ × ℤ) : ℚ :=
  if q.1 = q.2.2 ∧ q.2.1 = 0 then 1 / 2
  else if q.1 = q.2.1 ∧ q.2.1 = q.2.2 then 1 / 3 else 1

/-- Kronecker's `F_o(n)`, equation (4): the weighted number of reduced forms of
discriminant `-4n` with `a` or `c` odd.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, equation (4). -/
public def kroneckerFOdd (n : ℕ) : ℚ :=
  ∑ q ∈ (reducedFormsOfDiscriminant (-4 * n)).filter (fun q => Odd q.1 ∨ Odd q.2.2),
    reducedFormWeight q

/-- Kronecker's `F_e(n)`, equation (5): the weighted number of reduced forms of
discriminant `-4n` with `a` and `c` both even.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, equation (5). -/
public def kroneckerFEven (n : ℕ) : ℚ :=
  ∑ q ∈ (reducedFormsOfDiscriminant (-4 * n)).filter (fun q => Even q.1 ∧ Even q.2.2),
    reducedFormWeight q

/-- The fundamental discriminant `d(n)` attached to `n = 2 ^ α * g * h ^ 2` (`g, h` odd,
`g` squarefree), as a function of `α` and `g`: `-4g` if `α` is even and `g ≡ 1 (mod 4)`,
`-g` if `α` is even and `g ≡ 3 (mod 4)`, and `-8g` if `α` is odd.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1, after
equation (17). -/
public def kroneckerDiscriminant (α g : ℕ) : ℤ :=
  if Even α then (if g % 4 = 1 then -4 * g else -g) else -8 * g

/-- The multiplier `ℓ(n)` for `n = 2 ^ α * g * h ^ 2` with discriminant `d = d(n)`:
the product over the primes `p ∣ h` of
`(p ^ (v + 1) - 1) / (p - 1) - (d / p) * (p ^ v - 1) / (p - 1)`, `v = v_p(h)`, written
with geometric sums `∑_{i ≤ v} p ^ i` and `∑_{i < v} p ^ i`, and the Jacobi symbol
`(d / p)` (the Legendre symbol, since `p` is an odd prime).

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1, definition
of `ℓ(n)`. -/
public def kroneckerClassMultiplier (d : ℤ) (h : ℕ) : ℤ :=
  ∏ p ∈ h.primeFactors,
    ((∑ i ∈ Finset.range (h.factorization p + 1), (p : ℤ) ^ i) -
      jacobiSym d p * ∑ i ∈ Finset.range (h.factorization p), (p : ℤ) ^ i)

/-- Characteristic values of the class numbers: `h(-3) = h(-4) = h(-12) = 1` and
`H(-12) = 2` (the forms `x ^ 2 + 3y ^ 2` and the imprimitive `2x ^ 2 + 2xy + 2y ^ 2`).

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1. -/
public theorem gaussClassNumber_small :
    gaussClassNumber (-3) = 1 ∧ gaussClassNumber (-4) = 1 ∧ gaussClassNumber (-12) = 1 ∧
      unweightedHurwitzClassNumber (-12) = 2 := by
  decide +kernel

/-- Characteristic values of Kronecker's sums: `F_o(1) = 1 / 2`, `F_e(1) = 0`,
`F_o(3) = 1`, `F_e(3) = 1 / 3`.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, equations (4)
and (5). -/
public theorem kroneckerF_small :
    kroneckerFOdd 1 = 1 / 2 ∧ kroneckerFEven 1 = 0 ∧ kroneckerFOdd 3 = 1 ∧
      kroneckerFEven 3 = 1 / 3 := by
  decide +kernel

/-- Characteristic values of `d(n)` and `ℓ(n)`: `d = -4, -3, -8` for `(α, g) = (0, 1),
(0, 3), (1, 1)`; `ℓ = 1` for `h = 1`, and `ℓ = 5` for `d = -4`, `h = 3`.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1. -/
public theorem kroneckerDiscriminant_kroneckerClassMultiplier_small :
    kroneckerDiscriminant 0 1 = -4 ∧ kroneckerDiscriminant 0 3 = -3 ∧
      kroneckerDiscriminant 1 1 = -8 ∧ kroneckerClassMultiplier (-4) 1 = 1 ∧
      kroneckerClassMultiplier (-4) 3 = 5 := by
  decide +kernel

/-- Gauss's formula for `r₃(n)` as reformulated by Aygin and Williams: writing
`n = 2 ^ α * g * h ^ 2` with `g, h` odd and `g` squarefree,
`r₃(n) = k(n) ℓ(n) h(d(n))` with `k(n)` from Table 1: `6` (`α` even, `g = 1`), `8`
(`α` even, `g = 3`), `12` (`α` even, `g ≡ 1 (mod 4)`, `g ≠ 1`), `24` (`α` even,
`g ≡ 3 (mod 8)`, `g ≠ 3`), `0` (`α` even, `g ≡ 7 (mod 8)`), `12` (`α` odd).

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Theorem 1
(`integers-2026-A29-thm-1`). -/
public theorem_wanted threeSquareRepresentationCount_eq_kronecker_classNumber
    (n α g h : ℕ) (hn : n = 2 ^ α * g * h ^ 2) (hg : Odd g) (hgsq : Squarefree g)
    (hh : Odd h) :
    let L : ℤ := kroneckerClassMultiplier (kroneckerDiscriminant α g) h *
      gaussClassNumber (kroneckerDiscriminant α g)
    let r : ℤ := Nat.threeSquareRepresentationCount n
    (Even α → g = 1 → r = 6 * L) ∧
    (Even α → g = 3 → r = 8 * L) ∧
    (Even α → g % 4 = 1 → g ≠ 1 → r = 12 * L) ∧
    (Even α → g % 8 = 3 → g ≠ 3 → r = 24 * L) ∧
    (Even α → g % 8 = 7 → r = 0) ∧
    (Odd α → r = 12 * L)

/-- Main theorem: writing `n = 2 ^ α * g * h ^ 2` with `g, h` odd and `g` squarefree,
`F_o(n) = k_o(n) ℓ(n) h(d(n))` and `F_e(n) = k_e(n) ℓ(n) h(d(n))` with Table 2:
Case 1 (`α` even, `g = 1`): `2 ^ (α/2 - 1)`, `2 ^ (α/2 - 1) - 1/2`;
Case 2 (`α` even, `g = 3`): `2 ^ (α/2)`, `2 ^ (α/2) - 2/3`;
Case 3 (`α` even, `g ≡ 1 (mod 4)`, `g ≠ 1`): `2 ^ (α/2)`, `2 ^ (α/2) - 1`;
Case 4 (`α` even, `g ≡ 3 (mod 8)`, `g ≠ 3`): `3 · 2 ^ (α/2)`, `3 · 2 ^ (α/2) - 2`;
Case 5 (`α` even, `g ≡ 7 (mod 8)`): `2 ^ (α/2)`, `2 ^ (α/2)`;
Case 6 (`α` odd): `2 ^ ((α-1)/2)`, `2 ^ ((α-1)/2) - 1`.
`2 ^ (α/2 - 1)` is written `2 ^ (α / 2) / 2` in `ℚ` (it is `1/2` when `α = 0`).

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Theorem 2
(`integers-2026-A29-thm-2`). -/
public theorem_wanted kroneckerFOdd_kroneckerFEven_eq_classNumber
    (n α g h : ℕ) (hn : n = 2 ^ α * g * h ^ 2) (hg : Odd g) (hgsq : Squarefree g)
    (hh : Odd h) :
    let L : ℚ := (kroneckerClassMultiplier (kroneckerDiscriminant α g) h : ℚ) *
      gaussClassNumber (kroneckerDiscriminant α g)
    let t : ℚ := 2 ^ (α / 2)
    (Even α → g = 1 →
      kroneckerFOdd n = t / 2 * L ∧ kroneckerFEven n = (t / 2 - 1 / 2) * L) ∧
    (Even α → g = 3 →
      kroneckerFOdd n = t * L ∧ kroneckerFEven n = (t - 2 / 3) * L) ∧
    (Even α → g % 4 = 1 → g ≠ 1 →
      kroneckerFOdd n = t * L ∧ kroneckerFEven n = (t - 1) * L) ∧
    (Even α → g % 8 = 3 → g ≠ 3 →
      kroneckerFOdd n = 3 * t * L ∧ kroneckerFEven n = (3 * t - 2) * L) ∧
    (Even α → g % 8 = 7 →
      kroneckerFOdd n = t * L ∧ kroneckerFEven n = t * L) ∧
    (Odd α →
      kroneckerFOdd n = (2 : ℚ) ^ ((α - 1) / 2) * L ∧
        kroneckerFEven n = ((2 : ℚ) ^ ((α - 1) / 2) - 1) * L)

/-- Evaluation of the unweighted Hurwitz class number `H(-4n)`: writing
`n = 2 ^ α * g * h ^ 2` with `g, h` odd and `g` squarefree,
1. `α` even, `g = 1`: `H(-4n) = (2 ^ (α/2) - 1/2) ℓ(n) h(d(n)) + 1/2`;
2. `α` even, `g = 3`: `H(-4n) = (2 ^ (α/2 + 1) - 2/3) ℓ(n) h(d(n)) + 2/3`;
3. `α` even, `g ≠ 1`, `g ≡ 1 (mod 4)`: `H(-4n) = (2 ^ (α/2 + 1) - 1) ℓ(n) h(d(n))`;
4. `α` even, `g ≠ 3`, `g ≡ 3 (mod 8)`: `H(-4n) = (3 · 2 ^ (α/2 + 1) - 2) ℓ(n) h(d(n))`;
5. `α` even, `g ≡ 7 (mod 8)`: `H(-4n) = 2 ^ (α/2 + 1) ℓ(n) h(d(n))`;
6. `α` odd: `H(-4n) = (2 ^ ((α + 1)/2) - 1) ℓ(n) h(d(n))`.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Theorem 3
(`integers-2026-A29-thm-3`). -/
public theorem_wanted unweightedHurwitzClassNumber_neg_four_mul_eq_classNumber
    (n α g h : ℕ) (hn : n = 2 ^ α * g * h ^ 2) (hg : Odd g) (hgsq : Squarefree g)
    (hh : Odd h) :
    let L : ℚ := (kroneckerClassMultiplier (kroneckerDiscriminant α g) h : ℚ) *
      gaussClassNumber (kroneckerDiscriminant α g)
    let H : ℚ := unweightedHurwitzClassNumber (-4 * n)
    (Even α → g = 1 → H = ((2 : ℚ) ^ (α / 2) - 1 / 2) * L + 1 / 2) ∧
    (Even α → g = 3 → H = ((2 : ℚ) ^ (α / 2 + 1) - 2 / 3) * L + 2 / 3) ∧
    (Even α → g ≠ 1 → g % 4 = 1 → H = ((2 : ℚ) ^ (α / 2 + 1) - 1) * L) ∧
    (Even α → g ≠ 3 → g % 8 = 3 → H = (3 * (2 : ℚ) ^ (α / 2 + 1) - 2) * L) ∧
    (Even α → g % 8 = 7 → H = (2 : ℚ) ^ (α / 2 + 1) * L) ∧
    (Odd α → H = ((2 : ℚ) ^ ((α + 1) / 2) - 1) * L)

end

end MetaMathlibExt
