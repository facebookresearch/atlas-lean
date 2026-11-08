/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification

namespace MetaMathlibExt

@[expose] public section

open NumberField Filter Topology

/-- The set `T_K` of prime ideals `P` of `𝓞 K` lying above `2` with ramification index
`e(P|2) = 1` and inertia degree `f(P|2) = 1`.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Section 2 (definition of `T_K`). -/
def twoUnramifiedDegreeOnePrimes (K : Type*) [Field K] [NumberField K] : Set (Ideal (𝓞 K)) :=
  {P | P.IsPrime ∧ (2 : 𝓞 K) ∈ P ∧ P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1}

/-- Membership in `T_K`.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Section 2. -/
theorem mem_twoUnramifiedDegreeOnePrimes {K : Type*} [Field K] [NumberField K]
    (P : Ideal (𝓞 K)) :
    P ∈ twoUnramifiedDegreeOnePrimes K ↔
      P.IsPrime ∧ (2 : 𝓞 K) ∈ P ∧ P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1 :=
  Iff.rfl

/-- For a prime `P ∈ T_K` and every `n ≥ 1`, `𝓞_K / P^n ≃ ℤ / 2^n ℤ` as rings.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Lemma 1 (`integers-2026-A21-lem-1`). -/
public theorem_wanted ringOfIntegers_quotient_pow_ringEquiv_zmod_two_pow (K : Type*) [Field K]
    [NumberField K] (P : Ideal (𝓞 K)) (hP : P ∈ twoUnramifiedDegreeOnePrimes K) (n : ℕ)
    (hn : 1 ≤ n) :
    Nonempty ((𝓞 K ⧸ P ^ n) ≃+* ZMod (2 ^ n))

/-- The generalized fruit equation has no solution with even `x`: let `K` be a number field
with `T_K ≠ ∅`, let `a, b ∈ 𝓞_K \ {0}`, and let `c = 2ᵈ b - 3ʳ` with `r ≥ 2` odd and
`d ≥ 3` odd.  Then `a xᵈ - y² - z² + x y z - c = 0` has no solution `(x, y, z) ∈ 𝓞_K³` with
`2 ∣ x`.  Corrected reading: the record says "integers `r ≥ 2` and `d ≥ 3` odd", and is
false if `r` may be even: over `K = ℚ` with `a = b = 1`, `d = 3`, `r = 2` (so `c = -1`),
`(x, y, z) = (2, 3, 0)` is a solution.  The paper's proof (arXiv:2408.12278, proof of
Theorem 1) uses "since `r` is odd", so `odd` is read as applying to both `r` and `d`.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Theorem 1 (`integers-2026-A21-thm-1`). -/
public theorem_wanted generalizedFruit_no_solution_two_dvd (K : Type*) [Field K]
    [NumberField K] (hT : (twoUnramifiedDegreeOnePrimes K).Nonempty) (a b : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0) (r d : ℕ) (hr : 2 ≤ r) (hr' : Odd r) (hd : 3 ≤ d)
    (hd' : Odd d) (x y z : 𝓞 K) (hx : 2 ∣ x) :
    a * x ^ d - y ^ 2 - z ^ 2 + x * y * z - (2 ^ d * b - 3 ^ r) ≠ 0

/-- For a square-free integer `t ≠ 1` and the quadratic field `K = ℚ(√t)`, the set `T_K` is
nonempty if and only if `t ≡ 1 (mod 8)`.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Corollary 1 (`integers-2026-A21-cor-1`). -/
public theorem_wanted twoUnramifiedDegreeOnePrimes_nonempty_iff_quadratic (t : ℤ)
    (ht : Squarefree t) (ht1 : t ≠ 1) (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (α : K) (hα : α ^ 2 = t) :
    (twoUnramifiedDegreeOnePrimes K).Nonempty ↔ t ≡ 1 [ZMOD 8]

/-- The square-free positive integers `t ≡ 1 (mod 8)` have relative density `1/6` among the
square-free positive integers.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Theorem 2 (`integers-2026-A21-thm-2`). -/
public theorem_wanted squarefree_one_mod_eight_relativeDensity :
    Tendsto (fun X : ℕ =>
        ((Finset.Icc 1 X).filter (fun t => Squarefree t ∧ t % 8 = 1)).card /
          (((Finset.Icc 1 X).filter Squarefree).card : ℝ))
      atTop (𝓝 (1 / 6))

/-- Square-free integers in an arithmetic progression: for `r ∈ ℤ` and `N ≥ 1` with
`s = gcd(r, N)` square-free,
`#{t ≤ X : t ≡ r (mod N), t square-free} ~ φ(N)/(s φ(N/s) N) ∏_{q ∣ N} (1 - 1/q²)⁻¹ · (6/π²) X`,
the product over the primes `q` dividing `N`.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Theorem 3 (`integers-2026-A21-thm-3`),
quoted from their reference [2]. -/
public theorem_wanted squarefree_count_arithmeticProgression_isEquivalent (r : ℤ) (N : ℕ)
    (hN : 1 ≤ N) (hs : Squarefree (Int.gcd r N)) :
    Asymptotics.IsEquivalent atTop
      (fun X : ℝ =>
        (((Finset.Icc 1 ⌊X⌋₊).filter (fun t : ℕ => Squarefree t ∧ (t : ℤ) ≡ r [ZMOD N])).card : ℝ))
      (fun X : ℝ =>
        (N.totient : ℝ) / (Int.gcd r N * (N / Int.gcd r N).totient * N) *
          (∏ q ∈ N.primeFactors, (1 - 1 / (q : ℝ) ^ 2)⁻¹) * (6 / Real.pi ^ 2) * X)

/-- Integrality of torsion points of non-prime-power order: let `E/K` be an elliptic curve
given by a Weierstrass equation with coefficients in `𝓞_K`. If `P = (x, y) ∈ E(K)` is a torsion
point of order `m ≥ 2` that is not a prime power, then `x, y ∈ 𝓞_K`.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Theorem 5 (`integers-2026-A21-thm-5`),
quoted from Silverman, *The Arithmetic of Elliptic Curves*. -/
public theorem_wanted weierstrass_torsion_not_primePow_integral (K : Type*) [Field K]
    [NumberField K] [DecidableEq K] (W : WeierstrassCurve (𝓞 K)) [(W.baseChange K).IsElliptic] (x y : K)
    (h : (W.baseChange K).toAffine.Nonsingular x y)
    (hm : 2 ≤ addOrderOf (WeierstrassCurve.Affine.Point.some x y h))
    (hpp : ¬ IsPrimePow (addOrderOf (WeierstrassCurve.Affine.Point.some x y h))) :
    x ∈ Set.range (algebraMap (𝓞 K) K) ∧ y ∈ Set.range (algebraMap (𝓞 K) K)

/-- Nagell-Lutz integrality: for an elliptic curve `E : y² = x³ + A x + B` over `ℚ` with
`A, B ∈ ℤ`, every torsion point `P = (x, y) ∈ E(ℚ)` of order `m ≥ 2` has `x, y ∈ ℤ`.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Theorem 6 (`integers-2026-A21-thm-6`),
quoted from Silverman, *The Arithmetic of Elliptic Curves*. -/
public theorem_wanted short_weierstrass_torsion_integral (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (A B : ℤ) (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₄ : W.a₄ = A) (h₆ : W.a₆ = B)
    (x y : ℚ) (h : W.toAffine.Nonsingular x y)
    (hm : 2 ≤ addOrderOf (WeierstrassCurve.Affine.Point.some x y h)) :
    ∃ a b : ℤ, x = a ∧ y = b

/-- The curve `E_α : y² - α x y = x³ - (α² + 5)` of Theorem 4, as a Weierstrass curve
(`a₁ = -α`, `a₂ = a₃ = a₄ = 0`, `a₆ = -(α² + 5)`).

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Theorem 4, Equation (4.1). -/
public def fruitWeierstrassCurve {R : Type*} [CommRing R] (α : R) : WeierstrassCurve R :=
  ⟨-α, 0, 0, 0, -(α ^ 2 + 5)⟩

/-- The discriminant of `E_α` is `α⁸ + 5α⁶ - 432α⁴ - 4320α² - 10800`.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, proof of Theorem 4. -/
public theorem fruitWeierstrassCurve_Δ {R : Type*} [CommRing R] (α : R) :
    (fruitWeierstrassCurve α).Δ =
      α ^ 8 + 5 * α ^ 6 - 432 * α ^ 4 - 4320 * α ^ 2 - 10800 := by
  simp only [fruitWeierstrassCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- Let `K` be a number field with `T_K ≠ ∅` and `α ∈ 𝓞_K` not a root of
`x⁸ + 5x⁶ - 432x⁴ - 4320x² - 10800`. Then `E_α(K)` has no torsion point `P = (x₀, y₀) ≠ O`
whose order is not a prime power with `x₀ ∈ 𝓞_K` and `2 ∣ x₀`.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Corollary 2 (`integers-2026-A21-cor-2`). -/
public theorem_wanted fruitWeierstrassCurve_not_isOfFinOrder_of_two_dvd (K : Type*) [Field K]
    [NumberField K] [DecidableEq K] (hT : (twoUnramifiedDegreeOnePrimes K).Nonempty) (α : 𝓞 K)
    (hα : α ^ 8 + 5 * α ^ 6 - 432 * α ^ 4 - 4320 * α ^ 2 - 10800 ≠ 0) (x : 𝓞 K) (y : K)
    (h : (fruitWeierstrassCurve (algebraMap (𝓞 K) K α)).toAffine.Nonsingular
      (algebraMap (𝓞 K) K x) y)
    (hx : 2 ∣ x) (hfin : IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some _ _ h)) :
    IsPrimePow (addOrderOf (WeierstrassCurve.Affine.Point.some _ _ h))

/-- Over `ℚ`: for an integer `α` not a root of `x⁸ + 5x⁶ - 432x⁴ - 4320x² - 10800`, `E_α(ℚ)` has
no torsion point `P = (x₀, y₀) ≠ O` whose `x₀` has even numerator in lowest terms.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Corollary 3 (`integers-2026-A21-cor-3`). -/
public theorem_wanted fruitWeierstrassCurve_rat_not_isOfFinOrder_of_two_dvd_num (α : ℤ)
    (hα : α ^ 8 + 5 * α ^ 6 - 432 * α ^ 4 - 4320 * α ^ 2 - 10800 ≠ 0) (x y : ℚ)
    (h : (fruitWeierstrassCurve (α : ℚ)).toAffine.Nonsingular x y) (hx : 2 ∣ x.num) :
    ¬ IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some x y h)

end

end MetaMathlibExt
