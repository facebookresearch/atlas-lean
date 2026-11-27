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
public import MathlibExt.NumberTheory.GeneralizedFruitDiophantine
public import MathlibExt.NumberTheory.SquarefreeOneModEight

namespace MetaMathlibExt

@[expose] public section

open NumberField Filter Topology

/-- **Unramified degree-one primes above $2$ in quadratic fields.** Let $t \ne 1$ be a squarefree
integer, and let $K$ be a number field of degree $2$ over $\mathbb{Q}$ that contains an element
$\alpha$ with $\alpha^2 = t$, so that $K = \mathbb{Q}(\sqrt{t})$. Then the set $T_K$ of prime
ideals of the ring of integers $\mathcal{O}_K$ above $2$ with ramification index $1$ and inertia
degree $1$ is nonempty if and only if $t \equiv 1 \pmod{8}$.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Corollary 1 (`integers-2026-A21-cor-1`). -/
public theorem_wanted twoUnramifiedDegreeOnePrimes_nonempty_iff_quadratic (t : ℤ)
    (ht : Squarefree t) (ht1 : t ≠ 1) (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (α : K) (hα : α ^ 2 = t) :
    (twoUnramifiedDegreeOnePrimes K).Nonempty ↔ t ≡ 1 [ZMOD 8]

/-- **Square-free integers in an arithmetic progression.** Let $r \in \mathbb{Z}$ and let $N \ge 1$
be an integer such that $s = \gcd(r, N)$ is square-free. Then, as the real number $X \to \infty$,
the number of square-free integers $t$ with $1 \le t \le X$ and $t \equiv r \pmod N$ is
asymptotically equivalent to
$$
\frac{\varphi(N)}{s \, \varphi(N/s) \, N} \prod_{q \mid N} \left(1 - \frac{1}{q^2}\right)^{-1}
\frac{6}{\pi^2} X,
$$
where $\varphi$ is Euler's totient function and the product runs over the primes $q$ dividing $N$.

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

/-- **Torsion points of non-prime-power order are integral.** Let $K$ be a number field with ring
of integers $\mathcal{O}_K$, and let $E$ be a Weierstrass curve with coefficients in
$\mathcal{O}_K$ whose base change to $K$ is an elliptic curve. If $P = (x, y) \in E(K)$ is a
point of finite order $m \ge 2$ and $m$ is not a prime power, then $x$ and $y$ lie in
$\mathcal{O}_K$.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Theorem 5 (`integers-2026-A21-thm-5`),
quoted from Silverman, *The Arithmetic of Elliptic Curves*. -/
public theorem_wanted weierstrass_torsion_not_primePow_integral (K : Type*) [Field K]
    [NumberField K] [DecidableEq K] (W : WeierstrassCurve (𝓞 K)) [(W.baseChange K).IsElliptic]
    (x y : K) (h : (W.baseChange K).toAffine.Nonsingular x y)
    (hm : 2 ≤ addOrderOf (WeierstrassCurve.Affine.Point.some x y h))
    (hpp : ¬ IsPrimePow (addOrderOf (WeierstrassCurve.Affine.Point.some x y h))) :
    x ∈ Set.range (algebraMap (𝓞 K) K) ∧ y ∈ Set.range (algebraMap (𝓞 K) K)

/-- **Nagell–Lutz integrality.** Let $E : y^2 = x^3 + A x + B$ be an elliptic curve over
$\mathbb{Q}$ with $A, B \in \mathbb{Z}$. Every point $P = (x, y) \in E(\mathbb{Q})$ of finite order
$m \ge 2$ has $x, y \in \mathbb{Z}$.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Theorem 6 (`integers-2026-A21-thm-6`),
quoted from Silverman, *The Arithmetic of Elliptic Curves*. -/
public theorem_wanted short_weierstrass_torsion_integral (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (A B : ℤ) (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₄ : W.a₄ = A) (h₆ : W.a₆ = B)
    (x y : ℚ) (h : W.toAffine.Nonsingular x y)
    (hm : 2 ≤ addOrderOf (WeierstrassCurve.Affine.Point.some x y h)) :
    ∃ a b : ℤ, x = a ∧ y = b

/-- **The Weierstrass curve $E_\alpha$ of the generalized fruit equation.** For a commutative ring
$R$ and $\alpha \in R$, $E_\alpha$ is the Weierstrass curve over $R$ with coefficients
$a_1 = -\alpha$, $a_2 = a_3 = a_4 = 0$ and $a_6 = -(\alpha^2 + 5)$, that is, the curve
$y^2 - \alpha x y = x^3 - (\alpha^2 + 5)$.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Theorem 4, Equation (4.1). -/
public def fruitWeierstrassCurve {R : Type*} [CommRing R] (α : R) : WeierstrassCurve R :=
  ⟨-α, 0, 0, 0, -(α ^ 2 + 5)⟩

/-- **Discriminant of the curve $E_\alpha$.** For every commutative ring $R$ and every
$\alpha \in R$, the Weierstrass curve $E_\alpha : y^2 - \alpha x y = x^3 - (\alpha^2 + 5)$ over $R$
has discriminant $\alpha^8 + 5\alpha^6 - 432\alpha^4 - 4320\alpha^2 - 10800$.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, proof of Theorem 4. -/
public theorem fruitWeierstrassCurve_Δ {R : Type*} [CommRing R] (α : R) :
    (fruitWeierstrassCurve α).Δ =
      α ^ 8 + 5 * α ^ 6 - 432 * α ^ 4 - 4320 * α ^ 2 - 10800 := by
  simp only [fruitWeierstrassCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- **Torsion points of $E_\alpha$ with even integral $x$-coordinate have prime-power order.** Let
$K$ be a number field with ring of integers $\mathcal{O}_K$ such that some prime ideal of
$\mathcal{O}_K$ lying over $2$ has ramification index $1$ and inertia degree $1$ over $\mathbb{Z}$.
Let $\alpha \in \mathcal{O}_K$ satisfy
$\alpha^8 + 5\alpha^6 - 432\alpha^4 - 4320\alpha^2 - 10800 \neq 0$, and let $E_\alpha$ be the curve
$y^2 - \alpha x y = x^3 - (\alpha^2 + 5)$ over $K$. If $P = (x_0, y_0) \in E_\alpha(K)$ is a point
of finite order with $x_0 \in \mathcal{O}_K$ and $2 \mid x_0$ in $\mathcal{O}_K$, then the order of
$P$ is a prime power.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Corollary 2 (`integers-2026-A21-cor-2`). -/
public theorem_wanted fruitWeierstrassCurve_not_isOfFinOrder_of_two_dvd (K : Type*) [Field K]
    [NumberField K] [DecidableEq K] (hT : (twoUnramifiedDegreeOnePrimes K).Nonempty) (α : 𝓞 K)
    (hα : α ^ 8 + 5 * α ^ 6 - 432 * α ^ 4 - 4320 * α ^ 2 - 10800 ≠ 0) (x : 𝓞 K) (y : K)
    (h : (fruitWeierstrassCurve (algebraMap (𝓞 K) K α)).toAffine.Nonsingular
      (algebraMap (𝓞 K) K x) y)
    (hx : 2 ∣ x) (hfin : IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some _ _ h)) :
    IsPrimePow (addOrderOf (WeierstrassCurve.Affine.Point.some _ _ h))

/-- **Points of $E_\alpha(\mathbb{Q})$ with even numerator have infinite order.** Let $\alpha$ be an
integer with $\alpha^8 + 5\alpha^6 - 432\alpha^4 - 4320\alpha^2 - 10800 \neq 0$, and let $E_\alpha$
be the curve $y^2 - \alpha x y = x^3 - (\alpha^2 + 5)$ over $\mathbb{Q}$. If
$P = (x_0, y_0) \in E_\alpha(\mathbb{Q})$ is a point such that $x_0$, written in lowest terms, has
even numerator, then $P$ has infinite order.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Corollary 3 (`integers-2026-A21-cor-3`). -/
public theorem_wanted fruitWeierstrassCurve_rat_not_isOfFinOrder_of_two_dvd_num (α : ℤ)
    (hα : α ^ 8 + 5 * α ^ 6 - 432 * α ^ 4 - 4320 * α ^ 2 - 10800 ≠ 0) (x y : ℚ)
    (h : (fruitWeierstrassCurve (α : ℚ)).toAffine.Nonsingular x y) (hx : 2 ∣ x.num) :
    ¬ IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some x y h)

end

end MetaMathlibExt
