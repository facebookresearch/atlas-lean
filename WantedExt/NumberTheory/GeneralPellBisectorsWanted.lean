/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.Pell
public import MathlibExt.NumberTheory.Diophantine.BisectorEquationIntZero
public import MathlibExt.NumberTheory.Diophantine.NegativePellGcd
public import MathlibExt.NumberTheory.Diophantine.NegativePellRational
public import MathlibExt.NumberTheory.GeneralPellBisectors
public import MathlibExt.NumberTheory.GeneralPellBisectorsRatSolution
public import MathlibExt.NumberTheory.NegativePellDivisibility
public import MathlibExt.NumberTheory.GeneralPellBisectorsBisectorEquationFormTen

namespace MetaMathlibExt

@[expose] public section

/-- **Integer solutions of the bisector equation.** For a natural number $d > 1$ such that
$x^2 - d y^2 = -1$ has an integer solution, let $(X, Y)$ be its solution in positive integers
with $Y$ least, and define integers $f^{(d)}_k$ and $g^{(d)}_k$ by
$f^{(d)}_k + g^{(d)}_k \sqrt{d} = (X + Y \sqrt{d})^k$ for natural numbers $k$. Let $a, b, c$ be
integers with $|a| \ne |b|$ and
$$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1).$$
Then there is $s \in \{1, -1\}$ such that one of the following holds: there are a square-free
natural number $d > 1$ for which $x^2 - d y^2 = -1$ has an integer solution and natural numbers
$m, n > 0$ such that $(a, b, c)$ or $(b, a, c)$ equals
$$s \left(f^{(d)}_{(2m-1)(2n-1)}, \ f^{(d)}_{(2m-1)(2n+1)}, \
g^{(d)}_{(2m-1) 2n} / g^{(d)}_{2m-1}\right);$$
or there is a natural number $n > 0$ such that $(a, b, c)$ or $(b, a, c)$ equals
$$s \left(f^{(2)}_{2n-1}, \ -f^{(2)}_{2n+1}, \ f^{(2)}_{2n}\right).$$

Here $g^{(d)}_{(2m-1) 2n} / g^{(d)}_{2m-1}$ is the integer quotient; the division is exact.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 3 (`integers-2024-A111-thm-3`). -/
public theorem_wanted bisector_equation_int_solution (a b c : ℤ) (hab : |a| ≠ |b|)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ((∃ d m n : ℕ, 1 < d ∧ Squarefree d ∧ (∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) ∧ 0 < m ∧
          0 < n ∧
          let t : ℤ × ℤ × ℤ := (s * negPellF d ((2 * m - 1) * (2 * n - 1)),
            s * negPellF d ((2 * m - 1) * (2 * n + 1)),
            s * (negPellG d ((2 * m - 1) * (2 * n)) / negPellG d (2 * m - 1)))
          (a, b, c) = t ∨ (b, a, c) = t) ∨
        ∃ n : ℕ, 0 < n ∧
          let t : ℤ × ℤ × ℤ := (s * negPellF 2 (2 * n - 1), -(s * negPellF 2 (2 * n + 1)),
            s * negPellF 2 (2 * n))
          (a, b, c) = t ∨ (b, a, c) = t)

/-- **Bisector-equation solutions from the negative Pell sequences.** Let $d > 1$ be a natural
number such that $x^2 - d y^2 = -1$ has an integer solution, let $(X, Y)$ be its solution in
positive integers with $Y$ least, and define integers $f_k$ and $g_k$ by
$f_k + g_k \sqrt{d} = (X + Y \sqrt{d})^k$ for natural numbers $k$. Let $m, n > 0$ be natural
numbers and put $a = f_{(2m-1)(2n-1)}$, $b = f_{(2m-1)(2n+1)}$ and
$c = g_{(2m-1) 2n} / g_{2m-1}$. Then $g_{2m-1}$ divides $g_{(2m-1) 2n}$, so $c$ is an integer, and
$$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1).$$

Source: converse of Theorem 3 for Form (9); the square-freeness of $d$ is not needed here.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 3, converse for (9)
(`integers-2024-A111-thm-3`). -/
public theorem_wanted bisector_equation_form_nine (d m n : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (hm : 0 < m) (hn : 0 < n) :
    let a := negPellF d ((2 * m - 1) * (2 * n - 1))
    let b := negPellF d ((2 * m - 1) * (2 * n + 1))
    let c := negPellG d ((2 * m - 1) * (2 * n)) / negPellG d (2 * m - 1)
    negPellG d (2 * m - 1) ∣ negPellG d ((2 * m - 1) * (2 * n)) ∧
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)

/-- **Finitely many classes of solutions of a general Pell equation.** Let $d > 0$ be an integer
that is not a perfect square, let $\varepsilon$ be the fundamental solution of $x^2 - dy^2 = 1$,
viewed as a unit of $\mathbb{Z}[\sqrt d]$, and let $z \ne 0$ be an integer such that
$x^2 - dy^2 = z$ has an integral solution. Then there is a finite set $S$ of integral solutions
$(a, b)$ of $x^2 - dy^2 = z$ such that every integral solution $(x, y)$ satisfies
$x + y\sqrt d = \pm \varepsilon^n (a + b\sqrt d)$ in $\mathbb{Z}[\sqrt d]$ for some $(a, b) \in S$,
some sign and some $n \in \mathbb{Z}$.

The paper uses the fundamental unit of norm $\pm 1$; the powers of $\varepsilon$ are among its
powers, so this form implies the paper's.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 6 (quoting its reference [4,
Corollary 3.5]) (`integers-2024-A111-thm-6`). -/
public theorem_wanted generalPell_finitely_many_classes (d : ℤ) (hd₀ : 0 < d)
    (hd : ¬IsSquare d) (ε : Pell.Solution₁ d) (hε : Pell.IsFundamental ε) (z : ℤ) (hz : z ≠ 0)
    (hsol : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = z) :
    ∃ s : Finset (ℤ × ℤ), (∀ p ∈ s, p.1 ^ 2 - d * p.2 ^ 2 = z) ∧
      ∀ x y : ℤ, x ^ 2 - d * y ^ 2 = z → ∃ p ∈ s, ∃ n : ℤ, ∃ σ : ℤ√d, (σ = 1 ∨ σ = -1) ∧
        (⟨x, y⟩ : ℤ√d) = σ * ((ε ^ n : Pell.Solution₁ d) : ℤ√d) * ⟨p.1, p.2⟩

/-- **Basic properties of the negative Pell sequences.** Let $d > 1$ be a natural number such that
$x^2 - d y^2 = -1$ has an integral solution, let $(X, Y)$ be its solution in natural numbers with
least positive $Y$, and define integers $f_n, g_n$ by $(X + Y\sqrt{d})^n = f_n + g_n\sqrt{d}$.
Then $f_n^2 - d g_n^2 = (-1)^n$ for every $n \ge 0$, the sequence $(g_n)_{n \ge 0}$ is strictly
increasing, the sequence $(f_n)_{n \ge 1}$ is strictly increasing, and, with the real numbers
$\varepsilon = X + Y\sqrt{d}$ and $\varepsilon' = X - Y\sqrt{d}$, for every $n \ge 0$
$$f_n = \frac{\varepsilon^n + \varepsilon'^n}{2},$$
$$g_n = \frac{\varepsilon^n - \varepsilon'^n}{2\sqrt{d}}.$$

The sequence $(f_n)_{n \ge 0}$ is not strictly increasing when $d = 2$, since $f_0 = f_1 = 1$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5 (`integers-2024-A111-prop-5`). -/
public theorem_wanted negPell_sequences_basic (d : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) :
    (∀ n : ℕ, negPellF d n ^ 2 - d * negPellG d n ^ 2 = (-1) ^ n) ∧
      StrictMono (negPellG d) ∧ StrictMonoOn (negPellF d) (Set.Ici 1) ∧
      ∀ n : ℕ,
        (negPellF d n : ℝ) = ((negPellFundX d + negPellFundY d * √d) ^ n +
          (negPellFundX d - negPellFundY d * √d) ^ n) / 2 ∧
        (negPellG d n : ℝ) = ((negPellFundX d + negPellFundY d * √d) ^ n -
          (negPellFundX d - negPellFundY d * √d) ^ n) / (2 * √d)

/-- **Addition and doubling formulas for the negative Pell sequences.** Let $d$ be a natural
number such that $x^2 - dy^2 = -1$ has an integral solution, let $(X, Y)$ be the solution of
$x^2 - dy^2 = -1$ in natural numbers with the least positive $Y$, and let $f_n$ and $g_n$ be the
integers defined by $f_0 = 1$, $g_0 = 0$, $f_{n+1} = X f_n + dY g_n$ and
$g_{n+1} = Y f_n + X g_n$, so that $(X + Y\sqrt d)^n = f_n + g_n \sqrt d$. Then for all natural
numbers $n \le m$,
$$
\begin{aligned}
f_{m+n} &= f_m f_n + d g_m g_n, & g_{m+n} &= f_m g_n + g_m f_n, \\
f_{m-n} &= (-1)^n (f_m f_n - d g_m g_n), & g_{m-n} &= (-1)^{n+1} (f_m g_n - g_m f_n), \\
f_{2n} &= f_n^2 + d g_n^2, & g_{2n} &= 2 f_n g_n.
\end{aligned}
$$

The paper also assumes $d > 1$; this is not needed.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 6 (`integers-2024-A111-prop-6`). -/
public theorem_wanted negPell_addition_formulas (d : ℕ) (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1)
    (m n : ℕ) (hnm : n ≤ m) :
    negPellF d (m + n) = negPellF d m * negPellF d n + d * negPellG d m * negPellG d n ∧
      negPellG d (m + n) = negPellF d m * negPellG d n + negPellG d m * negPellF d n ∧
      negPellF d (m - n) =
        (-1) ^ n * (negPellF d m * negPellF d n - d * negPellG d m * negPellG d n) ∧
      negPellG d (m - n) =
        (-1) ^ (n + 1) * (negPellF d m * negPellG d n - negPellG d m * negPellF d n) ∧
      negPellF d (2 * n) = negPellF d n ^ 2 + d * negPellG d n ^ 2 ∧
      negPellG d (2 * n) = 2 * negPellF d n * negPellG d n

/-- **Sum and difference formulas for the negative Pell sequences.** Let $d$ be a natural number
such that $x^2 - d y^2 = -1$ has an integral solution, let $(X, Y)$ be its solution in natural
numbers with least positive $Y$, and define integers $f_n, g_n$ by
$(X + Y\sqrt{d})^n = f_n + g_n\sqrt{d}$, computed formally with $(\sqrt{d})^2 = d$. Let $m > n$
be natural numbers. If $n$ is even, then
$$f_{m+n} + f_{m-n} = 2 f_m f_n, \qquad f_{m+n} - f_{m-n} = 2 d g_m g_n,$$
$$g_{m+n} + g_{m-n} = 2 g_m f_n, \qquad g_{m+n} - g_{m-n} = 2 f_m g_n;$$
if $n$ is odd, then
$$f_{m+n} + f_{m-n} = 2 d g_m g_n, \qquad f_{m+n} - f_{m-n} = 2 f_m f_n,$$
$$g_{m+n} + g_{m-n} = 2 f_m g_n, \qquad g_{m+n} - g_{m-n} = 2 g_m f_n.$$

The source also assumes $d > 1$, which is not needed.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 7 (`integers-2024-A111-prop-7`). -/
public theorem_wanted negPell_sum_difference_formulas (d : ℕ)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (m n : ℕ) (hnm : n < m) :
    negPellF d (m + n) + negPellF d (m - n) =
        (if n % 2 = 0 then 2 * negPellF d m * negPellF d n
          else 2 * d * negPellG d m * negPellG d n) ∧
      negPellF d (m + n) - negPellF d (m - n) =
        (if n % 2 = 0 then 2 * d * negPellG d m * negPellG d n
          else 2 * negPellF d m * negPellF d n) ∧
      negPellG d (m + n) + negPellG d (m - n) =
        (if n % 2 = 0 then 2 * negPellG d m * negPellF d n
          else 2 * negPellF d m * negPellG d n) ∧
      negPellG d (m + n) - negPellG d (m - n) =
        (if n % 2 = 0 then 2 * negPellF d m * negPellG d n
          else 2 * negPellG d m * negPellF d n)


/-- **Coprimality of negative Pell terms whose indices have an even ratio.** Let $d > 1$ be a
natural number such that $x^2 - dy^2 = -1$ has an integral solution, let $(X, Y)$ be the solution
of $x^2 - dy^2 = -1$ in natural numbers with the least positive $Y$, and for each $n$ let $f_n$
and $g_n$ be the integers with $(X + Y\sqrt d)^n = f_n + g_n \sqrt d$. If $0 < n \le m$ are
natural numbers such that $n$ divides $m$ and $m / n$ is even, then $\gcd(f_m, f_n) = 1$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 11(b) (`integers-2024-A111-thm-11`). -/
public theorem_wanted negPellF_gcd_of_even_quotient (d : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (m n : ℕ) (hn : 0 < n) (hnm : n ≤ m)
    (hdvd : n ∣ m) (heven : Even (m / n)) :
    Int.gcd (negPellF d m) (negPellF d n) = 1

/-- **Divisibility between terms of the negative Pell sequence.** Let $d > 1$ be a natural
number such that $x^2 - dy^2 = -1$ has an integral solution, let $(X, Y)$ be the solution of
$x^2 - dy^2 = -1$ in natural numbers with the least positive $Y$, and for each $n$ let $f_n$ and
$g_n$ be the integers with $(X + Y\sqrt d)^n = f_n + g_n \sqrt d$. For natural numbers
$0 < n \le m$, $f_n$ divides $f_m$ if and only if either $d = 2$ and $n = 1$, or $n$ divides $m$
and $m / n$ is odd.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 11(c) (`integers-2024-A111-thm-11`). -/
public theorem_wanted negPellF_dvd_iff (d : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (m n : ℕ) (hn : 0 < n) (hnm : n ≤ m) :
    negPellF d n ∣ negPellF d m ↔ (d = 2 ∧ n = 1) ∨ (n ∣ m ∧ Odd (m / n))

open Classical in
/-- **Primes with strictly primitive representations.** For an integer $d$, $S(d)$ is the set of
primes $p$ for which there is an integer $l > 0$ such that $|x^2 - d y^2| = p^l$ has a strictly
primitive integral solution, that is, integers $x, y$ with $x$ and $d y$ coprime.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Notation 2
(`integers-2024-A111-thm-8`). -/
def strictPrimitivePrimes (d : ℤ) : Set ℕ :=
  {p | p.Prime ∧ ∃ l : ℕ, 0 < l ∧ ∃ x y : ℤ,
    IsCoprime x (d * y) ∧ |x ^ 2 - d * y ^ 2| = (p : ℤ) ^ l}

open Classical in
/-- **Strictly primitive exponent.** Let $d$ be an integer and $p$ a natural number, and let
$S(d)$ be the set of primes $q$ for which $|x^2 - d y^2| = q^l$ has a strictly primitive integral
solution (integers $x, y$ with $x$ and $d y$ coprime) for some integer $l > 0$. If $p \in S(d)$,
then $l_p$ is the least integer $l > 0$ such that $|x^2 - d y^2| = p^l$ has a strictly primitive
integral solution; if $p \notin S(d)$, then $l_p = 0$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Notation 2
(`integers-2024-A111-cor-1`). -/
noncomputable def strictPrimitiveExponent (d : ℤ) (p : ℕ) : ℕ :=
  if h : p ∈ strictPrimitivePrimes d then Nat.find h.2 else 0

open Classical in
/-- **Vanishing of the strictly primitive exponent.** Let $d$ be an integer and let $S(d)$ be the
set of primes $p$ for which $|x^2 - d y^2| = p^l$ has a strictly primitive integral solution
($x$ and $d y$ coprime) for some integer $l > 0$. Let $l_p$ be the least such $l$ when
$p \in S(d)$, and $l_p = 0$ otherwise. Then $l_p = 0$ for every natural number $p \notin S(d)$,
in particular for every $p$ that is not prime.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Notation 2
(`integers-2024-A111-cor-1`). -/
theorem strictPrimitiveExponent_of_not_mem {d : ℤ} {p : ℕ} (hp : p ∉ strictPrimitivePrimes d) :
    strictPrimitiveExponent d p = 0 := by
  simp [strictPrimitiveExponent, hp]

open Classical in
/-- **The strictly primitive exponent is attained.** Let $d$ be an integer and let $S(d)$ be the
set of primes $p$ for which $|x^2 - d y^2| = p^l$ has a strictly primitive integral solution
($x$ and $d y$ coprime) for some integer $l > 0$; for $p \in S(d)$ let $l_p$ be the least such
$l$. Then for every $p \in S(d)$, $l_p > 0$ and $|x^2 - d y^2| = p^{l_p}$ has a strictly
primitive integral solution.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Notation 2
(`integers-2024-A111-cor-1`). -/
theorem strictPrimitiveExponent_spec {d : ℤ} {p : ℕ} (hp : p ∈ strictPrimitivePrimes d) :
    0 < strictPrimitiveExponent d p ∧ ∃ x y : ℤ, IsCoprime x (d * y) ∧
      |x ^ 2 - d * y ^ 2| = (p : ℤ) ^ strictPrimitiveExponent d p := by
  have hl : strictPrimitiveExponent d p = Nat.find hp.2 := by simp [strictPrimitiveExponent, hp]
  rw [hl]
  exact Nat.find_spec hp.2

open Classical in
/-- **Minimality of the strictly primitive exponent.** Let $d$ be an integer and let $S(d)$ be the
set of primes $p$ for which $|x^2 - d y^2| = p^l$ has a strictly primitive integral solution
($x$ and $d y$ coprime) for some integer $l > 0$; for $p \in S(d)$ let $l_p$ be the least such
$l$. If $p \in S(d)$ and $l > 0$ is an integer for which $|x^2 - d y^2| = p^l$ has a strictly
primitive integral solution, then $l_p \le l$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Notation 2
(`integers-2024-A111-cor-1`). -/
theorem strictPrimitiveExponent_le {d : ℤ} {p l : ℕ} (hp : p ∈ strictPrimitivePrimes d)
    (hl : 0 < l) (h : ∃ x y : ℤ, IsCoprime x (d * y) ∧ |x ^ 2 - d * y ^ 2| = (p : ℤ) ^ l) :
    strictPrimitiveExponent d p ≤ l := by
  have he : strictPrimitiveExponent d p = Nat.find hp.2 := by simp [strictPrimitiveExponent, hp]
  rw [he]
  exact Nat.find_min' hp.2 ⟨hl, h⟩

/-- **$7$ is a strictly primitive prime for $d = 2$.** The prime $7$ belongs to $S(2)$, the set of
primes $p$ for which $|x^2 - 2 y^2| = p^l$ has a strictly primitive integral solution ($x$ and
$2 y$ coprime) for some integer $l > 0$. A witness is $3^2 - 2 \cdot 1^2 = 7$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Notation 2
(`integers-2024-A111-thm-8`). -/
theorem seven_mem_strictPrimitivePrimes_two : 7 ∈ strictPrimitivePrimes 2 :=
  ⟨by decide, 1, by norm_num, 3, 1, ⟨1, -1, by norm_num⟩, by norm_num⟩

open Classical in
/-- **The strictly primitive exponent of 7 for d = 2.** For $d = 2$ and $p = 7$, the strictly
primitive exponent $l_7$ equals $1$: the least integer $l > 0$ such that $|x^2 - 2 y^2| = 7^l$ has
an integral solution with $x$ and $2 y$ coprime exists and equals $1$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Notation 2
(`integers-2024-A111-cor-1`). -/
theorem strictPrimitiveExponent_two_seven : strictPrimitiveExponent 2 7 = 1 := by
  have hp := seven_mem_strictPrimitivePrimes_two
  have hl : strictPrimitiveExponent 2 7 = Nat.find hp.2 := by
    simp only [strictPrimitiveExponent, hp, dite_true]
  rw [hl]
  have h1 := (Nat.find_spec hp.2).1
  have h2 : Nat.find hp.2 ≤ 1 :=
    Nat.find_min' hp.2 ⟨Nat.one_pos, 3, 1, ⟨1, -1, by norm_num⟩, by norm_num⟩
  omega

/-- **Pythagorean parametrization of rational solutions of the bisector equation.** Let $a, b, c$
be rational numbers with $|a| \ne |b|$ and $(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1)$, and suppose
that $a^2 + 1$ and $b^2 + 1$ are squares of rational numbers. Then there are integers $l, m, n$ with
$|l| \ne |m|$, $l m \ne n^2$ and $l m n \ne 0$ such that
$$a = \frac{l^2 - n^2}{2 l n}, \qquad b = \frac{m^2 - n^2}{2 m n},$$
and
$$c = \frac{l m - n^2}{(l + m) n} \qquad \text{or} \qquad c = -\frac{(l + m) n}{l m - n^2}.$$

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 1(i)
(`integers-2024-A111-thm-1`). -/
public theorem_wanted bisector_equation_rat_solution_pythagorean (a b c : ℚ) (hab : |a| ≠ |b|)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1))
    (ha : ∃ a₂ : ℚ, a ^ 2 - a₂ ^ 2 = -1) (hb : ∃ b₂ : ℚ, b ^ 2 - b₂ ^ 2 = -1) :
    ∃ l m n : ℤ, |l| ≠ |m| ∧ l * m ≠ n ^ 2 ∧ l * m * n ≠ 0 ∧
      a = ((l : ℚ) ^ 2 - n ^ 2) / (2 * l * n) ∧ b = ((m : ℚ) ^ 2 - n ^ 2) / (2 * m * n) ∧
      (c = ((l : ℚ) * m - n ^ 2) / ((l + m) * n) ∨ c = -(((l : ℚ) + m) * n) / (l * m - n ^ 2))

/-- **Parametric rational solutions of the bisector equation.** Let $l, m, n$ be integers with
$|l| \ne |m|$, $l m \ne n^2$ and $l m n \ne 0$, and put
$$a = \frac{l^2 - n^2}{2 l n}, \qquad b = \frac{m^2 - n^2}{2 m n}.$$
Then each of the rational numbers
$$c = \frac{l m - n^2}{(l + m) n} \qquad \text{and} \qquad c = -\frac{(l + m) n}{l m - n^2}$$
satisfies $(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1)$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 1, converse
for (2) (`integers-2024-A111-thm-1`). -/
public theorem_wanted bisector_equation_form_two (l m n : ℤ) (hlm : |l| ≠ |m|)
    (hn2 : l * m ≠ n ^ 2) (h0 : l * m * n ≠ 0) :
    let a : ℚ := ((l : ℚ) ^ 2 - n ^ 2) / (2 * l * n)
    let b : ℚ := ((m : ℚ) ^ 2 - n ^ 2) / (2 * m * n)
    ∀ c ∈ ({((l : ℚ) * m - n ^ 2) / ((l + m) * n), -(((l : ℚ) + m) * n) / (l * m - n ^ 2)} :
        Set ℚ), (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)

/-- **Powers of strictly primitive solutions.** Let $d > 1$ be a square-free integer, $p$ an odd
prime, and $m, n > 0$ natural numbers. Write elements of $\mathbb{Z}[\sqrt{d}]$ as $u + v\sqrt{d}$
with integers $u, v$, and let $N(u + v\sqrt{d}) = u^2 - d v^2$ be the norm. If
$a = u + v\sqrt{d}$ satisfies $|N(a)| = p^m$ with $u$ and $d v$ coprime, then
$a^n = u' + v'\sqrt{d}$ satisfies $|N(a^n)| = p^{mn}$ with $u'$ and $d v'$ coprime; that is, $a^n$
gives a strictly primitive solution of $|x^2 - d y^2| = p^{mn}$.

The source states this without $p \ne 2$, and it fails for $p = 2$: for $d = 3$ and
$a = 1 + \sqrt{3}$ we have $N(a) = -2$, but $a^2 = 4 + 2\sqrt{3}$ and $\gcd(4, 6) = 2$. The sign
$\pm$ in the source's equation (14) is dropped.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 3(b)
(`integers-2024-A111-prop-3`). -/
public theorem_wanted strictlyPrimitive_pow (d : ℤ) (hd : 1 < d) (hsq : Squarefree d) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (a : ℤ√d)
    (ha : IsCoprime a.re (d * a.im)) (hN : |a.norm| = (p : ℤ) ^ m) :
    IsCoprime (a ^ n).re (d * (a ^ n).im) ∧ |(a ^ n).norm| = (p : ℤ) ^ (m * n)

/-- **Strictly primitive solutions modulo p and splitting of p.** Let $d > 1$ be a square-free
integer, let $K$ be a number field of degree $2$ over $\mathbb{Q}$ containing an element $s$ with
$s^2 = d$ (so $K = \mathbb{Q}(\sqrt d)$), and let $p$ be a prime such that $p \ne 2$, or
$d \equiv 1 \pmod 8$, or $d \equiv 2 \pmod 4$. Then there are integers $x, y$ with $x$ and $dy$
coprime and $p \mid x^2 - dy^2$ if and only if $p$ splits in $K$, that is, exactly two prime
ideals of the ring of integers of $K$ lie over $p$.

In the paper's terms: $|x^2 - dy^2| = z$ has a strictly primitive integral solution for some
multiple $z$ of $p$ exactly when $p$ splits. The paper requires only $p \ne 2$ or
$d \not\equiv 5 \pmod 8$; for $d \equiv 3 \pmod 4$ and $p = 2$ its statement fails: for $d = 3$,
$(x, y) = (1, 1)$ gives $|1 - 3| = 2$ with $\gcd(1, 3) = 1$, while $2$ ramifies in
$\mathbb{Q}(\sqrt 3)$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 7
(`integers-2024-A111-thm-7`). -/
public theorem_wanted exists_strictlyPrimitive_dvd_iff_split (d : ℤ) (hd : 1 < d)
    (hsq : Squarefree d) (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (s : K) (hs : s ^ 2 = d) (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2 ∨ d % 8 = 1 ∨ d % 4 = 2) :
    (∃ x y : ℤ, IsCoprime x (d * y) ∧ (p : ℤ) ∣ x ^ 2 - d * y ^ 2) ↔
      ((Ideal.span {(p : ℤ)}).primesOver (NumberField.RingOfIntegers K)).ncard = 2

/-- **Strictly primitive primes are the split primes.** Let $d > 1$ be a square-free integer, let
$K$ be any number field of degree $2$ over $\mathbb{Q}$ containing an element $s$ with $s^2 = d$,
and let $\mathcal{O}_K$ be its ring of integers. Suppose that $d \equiv 1 \pmod 8$, or that
$d \equiv 5 \pmod 8$ and every unit of $\mathcal{O}_K$ lies in $\mathbb{Z}[s]$, or that
$d \equiv 2 \pmod 4$. Then $S(d)$, the set of primes $p$ for which $|x^2 - d y^2| = p^l$ has an
integral solution with $x$ and $d y$ coprime for some integer $l > 0$, is the set of primes $p$
that split in $K$, that is, for which exactly two prime ideals of $\mathcal{O}_K$ lie over
$p\mathbb{Z}$.

Every unit of $\mathcal{O}_K$ lies in $\mathbb{Z}[s]$ exactly when the fundamental unit $\eta$ of
$K$ does, since the units are $\pm \eta^n$. The source also lists $d \equiv 3 \pmod 4$, where the
statement fails: $2 \in S(3)$ because $|1^2 - 3 \cdot 1^2| = 2$, but $2$ ramifies in
$\mathbb{Q}(\sqrt{3})$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 8(a)
(`integers-2024-A111-thm-8`). -/
public theorem_wanted strictPrimitivePrimes_eq_split (d : ℤ) (hd : 1 < d) (hsq : Squarefree d)
    (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (s : K) (hs : s ^ 2 = d)
    (hcase : d % 8 = 1 ∨ (d % 8 = 5 ∧ ∀ u : (NumberField.RingOfIntegers K)ˣ,
      ((u : NumberField.RingOfIntegers K) : K) ∈ Algebra.adjoin ℤ {s}) ∨ d % 4 = 2) :
    strictPrimitivePrimes d =
      {p : ℕ | p.Prime ∧
        ((Ideal.span {(p : ℤ)}).primesOver (NumberField.RingOfIntegers K)).ncard = 2}

/-- **Strictly primitive primes are 2 and the split primes.** Let $d > 1$ be a square-free
integer, let $K$ be any number field of degree $2$ over $\mathbb{Q}$ containing an element $s$
with $s^2 = d$, and let $\mathcal{O}_K$ be its ring of integers. Suppose that $d \equiv 5 \pmod 8$
and that some unit of $\mathcal{O}_K$ does not lie in $\mathbb{Z}[s]$ (equivalently, the
fundamental unit of $K$ does not lie in $\mathbb{Z}[s]$). Then $S(d)$, the set of primes $p$ for
which $|x^2 - d y^2| = p^l$ has an integral solution with $x$ and $d y$ coprime for some integer
$l > 0$, consists of $2$ together with the primes $p$ that split in $K$, that is, for which
exactly two prime ideals of $\mathcal{O}_K$ lie over $p\mathbb{Z}$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 8(b)
(`integers-2024-A111-thm-8`). -/
public theorem_wanted strictPrimitivePrimes_eq_split_insert_two (d : ℤ) (hd : 1 < d)
    (hsq : Squarefree d) (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (s : K) (hs : s ^ 2 = d) (h5 : d % 8 = 5)
    (hη : ∃ u : (NumberField.RingOfIntegers K)ˣ,
      ((u : NumberField.RingOfIntegers K) : K) ∉ Algebra.adjoin ℤ {s}) :
    strictPrimitivePrimes d = insert 2
      {p : ℕ | p.Prime ∧
        ((Ideal.span {(p : ℤ)}).primesOver (NumberField.RingOfIntegers K)).ncard = 2}

/-- **The strictly primitive exponent is at most the class number.** Let $d > 1$ be a squarefree
integer with $d \equiv 2$ or $d \equiv 3 \pmod 4$, and let $K$ be a number field of degree $2$
containing a square root of $d$ (so $K \cong \mathbb{Q}(\sqrt{d})$). Let $S(d)$ be the set of
primes $p$ for which $|x^2 - d y^2| = p^l$ has a strictly primitive integral solution ($x$ and
$d y$ coprime) for some integer $l > 0$, and for $p \in S(d)$ let $l_p$ be the least such $l$.
Then $l_p \le h_K$ for every $p \in S(d)$, where $h_K$ is the class number of $K$.

The source states this for all squarefree $d > 1$ except $d \equiv 1 \pmod 4$ with $p = 2$. For
$d \equiv 5 \pmod 8$ that is false: $\mathbb{Q}(\sqrt{37})$ has class number $1$, but $l_3 = 3$
for $d = 37$, since $8^2 - 37 \cdot 1^2 = 27$ while $|x^2 - 37 y^2| = 3$ and $|x^2 - 37 y^2| = 9$
have no strictly primitive solutions (the elements of norm $\pm 3$ and $\pm 9$ generating
primitive ideals are $(5 \pm \sqrt{37}) / 2$ and $(31 \pm 5\sqrt{37}) / 2$ times units, and all
units lie in $\mathbb{Z}[\sqrt{37}]$).

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Corollary 1
(`integers-2024-A111-cor-1`). -/
public theorem_wanted strictPrimitiveExponent_le_classNumber (d : ℤ) (hd : 1 < d)
    (hsq : Squarefree d) (hd4 : d % 4 = 2 ∨ d % 4 = 3) (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (s : K) (hs : s ^ 2 = d) (p : ℕ)
    (hp : p ∈ strictPrimitivePrimes d) :
    strictPrimitiveExponent d p ≤ NumberField.classNumber K

end

end MetaMathlibExt
