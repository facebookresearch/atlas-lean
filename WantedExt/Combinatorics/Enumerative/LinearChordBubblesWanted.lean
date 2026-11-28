/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.LinearChordBubbles
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Analysis.SpecialFunctions.Exp

namespace MetaMathlibExt

@[expose] public section

/-- **Total number of bubbles in linear chord diagrams.** For every natural number $n \ge 2$,
let $B_{n,p}$ be the total number of bubbles of size $p$ over all linear chord diagrams on $2n$
vertices. Then
$$\sum_{p=1}^{2n} B_{n,p} = \frac{(2n-2)!\,(4n-5)}{2^{n-1}\,(n-1)!}.$$

The hypothesis $n \ge 2$ is needed: for $n = 1$ the left side is $0$ and the right side is $-1$.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Lemma 3 (`jis-2024-24.4.2-lem-3`). -/
public theorem_wanted sum_bubbleCount (n : ℕ) (hn : 2 ≤ n) :
    (∑ p ∈ Finset.Icc 1 (2 * n), (bubbleCount n p : ℚ)) =
      (2 * n - 2).factorial * (4 * n - 5 : ℚ) / (2 ^ (n - 1) * (n - 1).factorial)

/-- **Formal contour-integral formula for bubble counts.** Let $G(s, w, y)$ be the power series
in $\mathbb{Q}[[s, w, y]]$ given by
$$G = \left(1 - \frac{y^2}{1 - sy + y^2}\right)^{-2} \left(\frac{1}{1 - wsy + w^2y^2} - 1\right),$$
and write $[s^a w^p y^m]\,G$ for its coefficient of $s^a w^p y^m$. For integers $n, p \ge 0$ let
$B_{n,p}$ be the total number of bubbles of size $p$ in all linear chord diagrams on $2n$
vertices. Then for all integers $n, p \ge 0$ (including $n = 0$)
$$\sum_{k \ge 0} \frac{(2k)!}{2^k\, k!}\, [s^{2k} w^p y^{2n}]\,G = B_{n,p} \quad\text{and}\quad
\sum_{k \ge 0} \frac{(2k)!}{2^k\, k!}\, [s^{2k} w^p y^{2n+1}]\,G = 0.$$

Each sum has only finitely many nonzero terms, since every power of $s$ in $G$ comes with at
least the same power of $y$. This is the termwise reading of the paper's formal contour
integral: integrating $x^{-1} e^{x^2/2} G(t/x, w, y)$ over $x$ and then replacing $t^{2k}$ by
$\int_0^\infty t^{2k} e^{-t}\,dt = (2k)!$ turns $s^{2k}$ into $(2k)!/(2^k k!)$. The literal
integrals diverge.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Theorem 1 (`jis-2024-24.4.2-thm-1`). -/
public theorem_wanted bubbleCount_formal_contour_integral :
    let s : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 0
    let w : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 1
    let y : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 2
    let G : MvPowerSeries (Fin 3) ℚ :=
      ((1 - y ^ 2 * (1 - s * y + y ^ 2)⁻¹) ^ 2)⁻¹ * ((1 - w * s * y + w ^ 2 * y ^ 2)⁻¹ - 1)
    (∀ n p : ℕ, (∑ᶠ k : ℕ, ((2 * k).factorial / (2 ^ k * k.factorial) : ℚ) *
        MvPowerSeries.coeff (Finsupp.single 0 (2 * k) + Finsupp.single 1 p +
          Finsupp.single 2 (2 * n)) G) = bubbleCount n p) ∧
    ∀ n p : ℕ, (∑ᶠ k : ℕ, ((2 * k).factorial / (2 ^ k * k.factorial) : ℚ) *
        MvPowerSeries.coeff (Finsupp.single 0 (2 * k) + Finsupp.single 1 p +
          Finsupp.single 2 (2 * n + 1)) G) = 0

/-- **Closed form of the bubble generating function.** In $\mathbb{Q}[[t, w, y]]$ let
$D = 1 - w(1 - wy)$ and let $I(t, w, y)$ be the power series
$$I = \frac{(1-w)^2 (1-wy)^2}{(1+w^2y)\,D^2}
\exp\!\left(\frac{y}{2}\left(\frac{tw}{1+w^2y}\right)^2\right) +
\left(\frac{(2 - w(y+2)(1 + y(1 - w(2-wy))))\,wy}{D^2} + \frac{(1-wy)\,t^2 w y^3}{D}\right)
\exp\!\left(\frac{t^2 y}{2}\right),$$
and write $[t^m w^p y^n]\,I$ for its coefficient of $t^m w^p y^n$. For integers $n, p \ge 0$ let
$B_{n,p}$ be the total number of bubbles of size $p$ in all linear chord diagrams on $2n$
vertices. Then for all integers $n \ge 1$ and $p \ge 0$
$$\sum_{m \ge 0} m!\, [t^m w^p y^n]\,I = B_{n,p}.$$

The sum has only finitely many nonzero terms, since $t$ occurs in $I$ only as $t^2$ times a
factor $y$. Replacing $t^m$ by $m! = \int_0^\infty t^m e^{-t}\,dt$ reads the formula as a formal
Laplace transform in $t$, as in the paper's proofs of Lemmas 3 and 4, so that the left side is
the coefficient of $y^n w^p$ of the paper's $B(y, w) = \sum_{n,p} B_{n,p} y^n w^p$. The case
$n = 0$ is excluded: the printed formula has constant term $1$ while $B_{0,0} = 0$ (the paper's
residue computation in its contour variable $x$ omits the residue $-1$ at $x = 0$; Theorem 1
gives constant term $0$).

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Corollary 2 (`jis-2024-24.4.2-cor-2`). -/
public theorem_wanted bubbleCount_formal_laplace_closed_form :
    let t : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 0
    let w : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 1
    let y : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.X 2
    let D : MvPowerSeries (Fin 3) ℚ := 1 - w * (1 - w * y)
    let integrand : MvPowerSeries (Fin 3) ℚ :=
      (1 - w) ^ 2 * (1 - w * y) ^ 2 * ((1 + w ^ 2 * y) * D ^ 2)⁻¹ *
          PowerSeries.subst ((2⁻¹ : ℚ) • (y * (t * w * (1 + w ^ 2 * y)⁻¹) ^ 2))
            (PowerSeries.exp ℚ) +
        ((2 - w * (y + 2) * (1 + y * (1 - w * (2 - w * y)))) * (D ^ 2)⁻¹ * (w * y) +
            (1 - w * y) * D⁻¹ * (t ^ 2 * w * y ^ 3)) *
          PowerSeries.subst ((2⁻¹ : ℚ) • (t ^ 2 * y)) (PowerSeries.exp ℚ)
    ∀ n p : ℕ, 1 ≤ n →
      (∑ᶠ m : ℕ, (m.factorial : ℚ) *
        MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 p + Finsupp.single 2 n)
          integrand) = bubbleCount n p

/-- **Limiting density of bubble sizes in linear chord diagrams.** Let $B_{n,p}$ be the total
number of bubbles of size $p$ over all linear chord diagrams on $2n$ vertices. Let $x$ be a real
number with $0 < x \le 2$, and let $(p_n)_{n \ge 0}$ be natural numbers with $p_0 = 0$,
$p_n \le 2n - 2$ for every $n \ge 1$, and $p_n / (n - 1) \to x$ as $n \to \infty$. Then
$$\frac{(n-1)\,B_{n,p_n}}{\sum_{p=1}^{2n-2} B_{n,p}} \to \frac{e\,(6-x)}{2\,(4e-2)}\,e^{-x/2}$$
as $n \to \infty$. The sum in the denominator leaves out the bubble sizes $2n - 1$ and $2n$; a
bubble of size $2n$ is a whole diagram without short chords.

The paper writes $B_{n,x(n-1)}$; since $x(n-1)$ need not be an integer, the limit is read along
integer sizes $p_n$ with $p_n/(n-1) \to x$, the scaling the paper's proof uses.

Source: Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer
Sequences 27 (2024), Article 24.4.2, Theorem 6 (`jis-2024-24.4.2-thm-6`). -/
public theorem_wanted tendsto_bubbleCount_density (x : ℝ) (hx0 : 0 < x) (hx2 : x ≤ 2)
    (p : ℕ → ℕ) (hp : ∀ n, p n ≤ 2 * n - 2)
    (hpx : Filter.Tendsto (fun n : ℕ => (p n : ℝ) / ((n : ℝ) - 1)) Filter.atTop (nhds x)) :
    Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) - 1) * bubbleCount n (p n) /
        ∑ q ∈ Finset.Icc 1 (2 * n - 2), (bubbleCount n q : ℝ))
      Filter.atTop
      (nhds (Real.exp 1 * (6 - x) / (2 * (4 * Real.exp 1 - 2)) * Real.exp (-x / 2)))

end

end MetaMathlibExt
