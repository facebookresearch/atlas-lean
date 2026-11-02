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

namespace MetaMathlibExt

@[expose] public section

open Classical in
/-- **Second coordinate of the fundamental negative Pell solution.** For a natural number $d$,
$Y$ is the least positive integer $y$ such that $x^2 - d y^2 = -1$ for some integer $x$, and
$Y = 0$ when there is no such $y$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)-(24)
(`integers-2024-A111-prop-5`). -/
noncomputable def negPellFundY (d : ℕ) : ℕ :=
  if h : ∃ y : ℕ, 0 < y ∧ ∃ x : ℕ, x ^ 2 + 1 = d * y ^ 2 then Nat.find h else 0

/-- **First coordinate of the fundamental negative Pell solution.** For a natural number $d$, let
$Y$ be the least positive integer $y$ such that $x^2 - d y^2 = -1$ for some integer $x$, or $0$
if there is no such $y$. Then $X = \lfloor \sqrt{d Y^2 - 1} \rfloor$, where $d Y^2 - 1$ is read
as $0$ when $d Y^2 = 0$. So $X$ is the nonnegative integer with $X^2 - d Y^2 = -1$ when a solution
exists, and $X = 0$ otherwise.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)-(24)
(`integers-2024-A111-prop-5`). -/
noncomputable def negPellFundX (d : ℕ) : ℕ :=
  Nat.sqrt (d * negPellFundY d ^ 2 - 1)

open Classical in
/-- **The fundamental negative Pell solution solves the equation.** Let $d$ be a natural number
such that $x^2 - d y^2 = -1$ has a solution in a natural number $x$ and a positive integer $y$.
Then the fundamental solution $(X, Y)$, the one with the least positive $y$, satisfies $Y > 0$
and $X^2 + 1 = d Y^2$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (24)
(`integers-2024-A111-prop-5`). -/
theorem negPellFund_spec {d : ℕ} (h : ∃ y : ℕ, 0 < y ∧ ∃ x : ℕ, x ^ 2 + 1 = d * y ^ 2) :
    0 < negPellFundY d ∧ negPellFundX d ^ 2 + 1 = d * negPellFundY d ^ 2 := by
  have hY : negPellFundY d = Nat.find h := by simp [negPellFundY, h]
  obtain ⟨hpos, x, hx⟩ := Nat.find_spec h
  rw [← hY] at hpos hx
  refine ⟨hpos, ?_⟩
  have : d * negPellFundY d ^ 2 - 1 = x ^ 2 := by omega
  simp only [negPellFundX, this, Nat.sqrt_eq']
  exact hx

open Classical in
/-- **Minimality of the fundamental negative Pell solution.** Let $d$ be a natural number and let
$Y$ be the second coordinate of its fundamental negative Pell solution. If $y$ is a positive
integer such that $x^2 - d y^2 = -1$ for some natural number $x$, then $Y \le y$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (24)
(`integers-2024-A111-prop-5`). -/
theorem negPellFundY_le {d y : ℕ} (hy : 0 < y) (hx : ∃ x : ℕ, x ^ 2 + 1 = d * y ^ 2) :
    negPellFundY d ≤ y := by
  have h : ∃ y : ℕ, 0 < y ∧ ∃ x : ℕ, x ^ 2 + 1 = d * y ^ 2 := ⟨y, hy, hx⟩
  have hY : negPellFundY d = Nat.find h := by simp [negPellFundY, h]
  rw [hY]
  exact Nat.find_min' h ⟨hy, hx⟩

open Classical in
/-- **The fundamental solution of the negative Pell equation for d = 2.** The least positive
integer $y$ such that $x^2 - 2 y^2 = -1$ for some integer $x$ is $Y = 1$, and the corresponding
first coordinate is $X = 1$; that is, the fundamental solution for $d = 2$ is $(1, 1)$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)-(24)
(`integers-2024-A111-prop-5`). -/
theorem negPellFund_two : negPellFundY 2 = 1 ∧ negPellFundX 2 = 1 := by
  have h : ∃ y : ℕ, 0 < y ∧ ∃ x : ℕ, x ^ 2 + 1 = 2 * y ^ 2 := ⟨1, by norm_num, 1, by norm_num⟩
  have hY : negPellFundY 2 = 1 := by
    simp only [negPellFundY, h, dite_true]
    rw [Nat.find_eq_iff]
    exact ⟨⟨by norm_num, 1, by norm_num⟩, fun n hn ⟨hn0, _⟩ => by omega⟩
  refine ⟨hY, ?_⟩
  simp [negPellFundX, hY]

/-- **First coordinates of the powers of the fundamental negative Pell solution.** For a natural
number $d$, let $Y$ be the least positive integer $y$ such that $x^2 - d y^2 = -1$ for some
integer $x$, let $X$ be the nonnegative integer with $X^2 - d Y^2 = -1$, and set $X = Y = 0$
when there is no such $y$. In the ring $\mathbb{Z}[\sqrt{d}]$ of formal expressions
$a + b \sqrt{d}$ with $a, b \in \mathbb{Z}$ and $(\sqrt{d})^2 = d$, put
$\varepsilon = X + Y \sqrt{d}$. For $n \ge 0$, $f_n$ is the integer such that
$\varepsilon^n = f_n + g_n \sqrt{d}$ for some integer $g_n$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)
(`integers-2024-A111-prop-5`). -/
noncomputable def negPellF (d n : ℕ) : ℤ :=
  ((⟨negPellFundX d, negPellFundY d⟩ : ℤ√(d : ℤ)) ^ n).re

/-- **Second coordinates of the powers of the fundamental negative Pell solution.** For a natural
number $d$, let $Y$ be the least positive integer $y$ such that $x^2 - d y^2 = -1$ for some
integer $x$, let $X$ be the nonnegative integer with $X^2 - d Y^2 = -1$, and set $X = Y = 0$
when there is no such $y$. In the ring $\mathbb{Z}[\sqrt{d}]$ of formal expressions
$a + b \sqrt{d}$ with $a, b \in \mathbb{Z}$ and $(\sqrt{d})^2 = d$, put
$\varepsilon = X + Y \sqrt{d}$. For $n \ge 0$, $g_n$ is the integer such that
$\varepsilon^n = f_n + g_n \sqrt{d}$ for some integer $f_n$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)
(`integers-2024-A111-prop-5`). -/
noncomputable def negPellG (d n : ℕ) : ℤ :=
  ((⟨negPellFundX d, negPellFundY d⟩ : ℤ√(d : ℤ)) ^ n).im

/-- **Initial values of the negative Pell sequences.** For every natural number $d$, the
sequences $f_n$ and $g_n$ of the negative Pell equation $x^2 - d y^2 = -1$ satisfy $f_0 = 1$ and
$g_0 = 0$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)
(`integers-2024-A111-prop-5`). -/
@[simp]
theorem negPellF_zero_negPellG_zero (d : ℕ) : negPellF d 0 = 1 ∧ negPellG d 0 = 0 := by
  simp [negPellF, negPellG]

/-- **Recurrence for the negative Pell sequences.** Let $d$ be a natural number, let $(X, Y)$ be the
solution of $x^2 - d y^2 = -1$ in natural numbers with least positive $Y$ (with $X = Y = 0$ if
there is none), and define integers $f_n, g_n$ by $(X + Y\sqrt{d})^n = f_n + g_n\sqrt{d}$,
computed formally with $(\sqrt{d})^2 = d$. Then for every $n \ge 0$,
$$f_{n+1} = f_n X + d g_n Y, \qquad g_{n+1} = f_n Y + g_n X.$$

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)
(`integers-2024-A111-prop-5`). -/
theorem negPell_succ (d n : ℕ) :
    negPellF d (n + 1) = negPellF d n * negPellFundX d + d * negPellG d n * negPellFundY d ∧
      negPellG d (n + 1) = negPellF d n * negPellFundY d + negPellG d n * negPellFundX d := by
  simp [negPellF, negPellG, pow_succ]

/-- **The negative Pell sequences for d = 2 at n = 1.** Let $(X, Y)$ be the solution of
$x^2 - 2y^2 = -1$ in natural numbers with the least positive $Y$, and for each $n$ let $f_n$ and
$g_n$ be the integers with $(X + Y\sqrt 2)^n = f_n + g_n \sqrt 2$. Then $f_1 = g_1 = 1$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)
(`integers-2024-A111-prop-5`). -/
theorem negPellF_two_one : negPellF 2 1 = 1 ∧ negPellG 2 1 = 1 := by
  simp [negPellF, negPellG, negPellFund_two]

/-- **Angle bisectors satisfy the bisector equation.** Let $a, b, c$ be real numbers with
$|a| \ne |b|$ and $c \ne 0$, and suppose that the lines $y = cx$ and $y = -c^{-1} x$ both bisect
the angles between the lines $y = ax$ and $y = bx$, that is,
$$
\frac{|a - c|}{\sqrt{a^2 + 1}} = \frac{|b - c|}{\sqrt{b^2 + 1}} \quad\text{and}\quad
\frac{|a + c^{-1}|}{\sqrt{a^2 + 1}} = \frac{|b + c^{-1}|}{\sqrt{b^2 + 1}}.
$$
Then $(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1)$.

A line $y = sx$ bisects the angles between $y = ax$ and $y = bx$ exactly when the point $(1, s)$
is equidistant from both lines, that is, when $|a - s| / \sqrt{a^2 + 1} = |b - s| / \sqrt{b^2 + 1}$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 1(a)
(`integers-2024-A111-prop-1`). -/
public theorem_wanted bisector_slope_equation (a b c : ℝ) (hab : |a| ≠ |b|) (hc : c ≠ 0)
    (hbis : |a - c| / √(a ^ 2 + 1) = |b - c| / √(b ^ 2 + 1))
    (hbis' : |a + c⁻¹| / √(a ^ 2 + 1) = |b + c⁻¹| / √(b ^ 2 + 1)) :
    (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)

/-- **Rational solutions of the bisector equation.** Let $a, b, c$ be rational numbers with
$|a| \ne |b|$ and $(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1)$. Then there are a square-free
natural number $d > 0$ and rational numbers $a_2, b_2$ with $a^2 - d a_2^2 = -1$ and
$b^2 - d b_2^2 = -1$ such that either $a_2 + b_2 \ne 0$ and
$c = (a b_2 + a_2 b) / (a_2 + b_2)$, or $b_2 - a_2 \ne 0$ and $c = (a b_2 - a_2 b) / (b_2 - a_2)$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 1(b)
(`integers-2024-A111-prop-1`). -/
public theorem_wanted bisector_equation_rat_solution (a b c : ℚ) (hab : |a| ≠ |b|)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) :
    ∃ d : ℕ, 0 < d ∧ Squarefree d ∧ ∃ a₂ b₂ : ℚ, a ^ 2 - d * a₂ ^ 2 = -1 ∧
      b ^ 2 - d * b₂ ^ 2 = -1 ∧
      ((b₂ + a₂ ≠ 0 ∧ c = (a * b₂ + a₂ * b) / (b₂ + a₂)) ∨
        (b₂ - a₂ ≠ 0 ∧ c = (a * b₂ - a₂ * b) / (b₂ - a₂)))

/-- **Symmetries of the bisector equation.** Let $a, b, c$ be real numbers with
$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1)$. Then the triples $(-a, -b, -c)$ and $(b, a, c)$
satisfy the same equation, and so does $(a, b, -c^{-1})$ when $c \ne 0$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 2(a)
(`integers-2024-A111-prop-2`). -/
public theorem_wanted bisector_equation_symm (a b c : ℝ)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) :
    (c ≠ 0 → (a - -c⁻¹) ^ 2 * (b ^ 2 + 1) = (b - -c⁻¹) ^ 2 * (a ^ 2 + 1)) ∧
      (-a - -c) ^ 2 * ((-b) ^ 2 + 1) = (-b - -c) ^ 2 * ((-a) ^ 2 + 1) ∧
      (b - c) ^ 2 * (a ^ 2 + 1) = (a - c) ^ 2 * (b ^ 2 + 1)

/-- **No nontrivial integer solutions of the bisector equation with $a = 0$ or $b = 0$.** Let
$a, b, c$ be integers with $a = 0$ or $b = 0$ and
$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1)$. Then $|a| = |b|$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 2(b)
(`integers-2024-A111-prop-2`). -/
public theorem_wanted bisector_equation_int_zero (a b c : ℤ) (h0 : a = 0 ∨ b = 0)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) : |a| = |b|

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

/-- **Bisector-equation solutions from the powers of $1 + \sqrt{2}$.** The least solution of
$x^2 - 2 y^2 = -1$ in positive integers is $(1, 1)$; define integers $f_k$ and $g_k$ by
$f_k + g_k \sqrt{2} = (1 + \sqrt{2})^k$ for natural numbers $k$. For every natural number $n > 0$,
the integers $a = f_{2n-1}$, $b = -f_{2n+1}$ and $c = f_{2n}$ satisfy
$$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1).$$

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 3, converse for (10)
(`integers-2024-A111-thm-3`). -/
public theorem_wanted bisector_equation_form_ten (n : ℕ) (hn : 0 < n) :
    let a := negPellF 2 (2 * n - 1)
    let b := -negPellF 2 (2 * n + 1)
    let c := negPellF 2 (2 * n)
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

/-- **Rational solvability of the negative Pell equation.** For a positive squarefree integer
$d$, the equation $x^2 - d y^2 = -1$ has a rational solution if and only if no prime divisor of
$d$ is congruent to $3$ modulo $4$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 5 (`integers-2024-A111-thm-5`). -/
public theorem_wanted negPell_rat_solvable_iff (d : ℕ) (hd : 0 < d) (hsq : Squarefree d) :
    (∃ x y : ℚ, x ^ 2 - d * y ^ 2 = -1) ↔ ∀ p : ℕ, p.Prime → p ∣ d → p % 4 ≠ 3

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

/-- **Comparison of the negative Pell sequences.** Let $d > 1$ be a natural number such that
$x^2 - d y^2 = -1$ has an integer solution, let $(X, Y)$ be its fundamental solution (the one with
$X, Y > 0$ and $Y$ least), and write $(X + Y \sqrt{d})^n = f_n + g_n \sqrt{d}$. Then for every
$n \ge 0$, $g_n \le f_n$, with equality if and only if $d = 2$ and $n = 1$.

Only the first sentence of the source's corollary is stated here: its second sentence, printed as
$f_1 \ge d - 1$ with a displaced square root sign, fails when read literally at $d = 5$, where
$f_1 = 2$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Corollary 2, first sentence
(`integers-2024-A111-cor-2`). -/
public theorem_wanted negPellG_le_negPellF (d : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (n : ℕ) :
    negPellG d n ≤ negPellF d n ∧ (negPellF d n = negPellG d n ↔ d = 2 ∧ n = 1)

/-- **Coprimality of the negative Pell sequences.** Let $d > 1$ be a natural number such that
$x^2 - d y^2 = -1$ has an integral solution, let $(X, Y)$ be its solution in natural numbers with
least positive $Y$, and define integers $f_n, g_n$ by $(X + Y\sqrt{d})^n = f_n + g_n\sqrt{d}$.
Then for every $n > 0$, $\gcd(d, f_n) = 1$ and $\gcd(f_n, g_n) = 1$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 11(a) (`integers-2024-A111-thm-11`). -/
public theorem_wanted negPell_gcd_eq_one (d : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (n : ℕ) (hn : 0 < n) :
    Int.gcd d (negPellF d n) = 1 ∧ Int.gcd (negPellF d n) (negPellG d n) = 1

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

/-- **Divisibility of the second coordinates of negative Pell powers.** Let $d > 1$ be a natural
number such that $x^2 - d y^2 = -1$ has an integer solution, let $(X, Y)$ be its fundamental
solution (the one with $X, Y > 0$ and $Y$ least), and write
$(X + Y \sqrt{d})^n = f_n + g_n \sqrt{d}$. For natural numbers $0 < n \le m$, $g_n$ divides $g_m$
if and only if $n$ divides $m$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 11(d) (`integers-2024-A111-thm-11`). -/
public theorem_wanted negPellG_dvd_iff (d : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (m n : ℕ) (hn : 0 < n) (hnm : n ≤ m) :
    negPellG d n ∣ negPellG d m ↔ n ∣ m

/-- **$|x^2 - d y^2|$ is never $2 \bmod 4$ when $d \equiv 1 \pmod 4$.** Let $d$ and $z$ be integers
with $d \equiv 1 \pmod 4$ and $z \equiv 2 \pmod 4$. Then $|x^2 - d y^2| \ne z$ for all integers $x$
and $y$.

Source: the source's hypothesis $z > 1$ is not needed. The second sentence of part (a) (on $S(d)$
and $l_2$) is not formalized.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Lemma 1(a), first sentence
(`integers-2024-A111-lem-1`). -/
public theorem_wanted abs_sq_sub_mul_sq_ne_of_two_mod_four (d z : ℤ) (hd : d % 4 = 1)
    (hz : z % 4 = 2) (x y : ℤ) : |x ^ 2 - d * y ^ 2| ≠ z

/-- **Solutions of |x² − dy²| = z are even when d ≡ 1 and z ≡ 4 (mod 8).** Let $d$ and $z$ be
integers with $d \equiv 1 \pmod 8$ and $z \equiv 4 \pmod 8$. If integers $x$ and $y$ satisfy
$|x^2 - dy^2| = z$, then $x$ and $y$ are both even.

The paper also assumes $z > 1$; this is not needed. The second sentence of part (c) of the
paper's lemma, on the fundamental unit, is not formalized.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Lemma 1(c), first sentence
(`integers-2024-A111-lem-1`). -/
public theorem_wanted even_of_abs_sq_sub_mul_sq_four_mod_eight (d z : ℤ) (hd : d % 8 = 1)
    (hz : z % 8 = 4) (x y : ℤ) (h : |x ^ 2 - d * y ^ 2| = z) : Even x ∧ Even y

/-- **Solutions of |x² − dy²| = z are even when d ≡ 5 and z ≡ 0 (mod 8).** Let $d$ and $z$ be
integers with $d \equiv 5 \pmod 8$ and $z \equiv 0 \pmod 8$. If integers $x$ and $y$ satisfy
$|x^2 - dy^2| = z$, then $x$ and $y$ are both even.

The paper also assumes $z > 1$; this is not needed.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Lemma 1(d) (`integers-2024-A111-lem-1`). -/
public theorem_wanted even_of_abs_sq_sub_mul_sq_zero_mod_eight (d z : ℤ) (hd : d % 8 = 5)
    (hz : z % 8 = 0) (x y : ℤ) (h : |x ^ 2 - d * y ^ 2| = z) : Even x ∧ Even y

open Classical in
/-- **Primes with strictly primitive representations.** For an integer $d$, $S(d)$ is the set of
primes $p$ for which there is an integer $l > 0$ such that $|x^2 - d y^2| = p^l$ has a strictly
primitive integral solution, that is, integers $x, y$ with $x$ and $d y$ coprime.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Notation 2
(`integers-2024-A111-thm-8`). -/
def strictPrimitivePrimes (d : ℤ) : Set ℕ :=
  {p | p.Prime ∧ ∃ l : ℕ, 0 < l ∧ ∃ x y : ℤ, IsCoprime x (d * y) ∧ |x ^ 2 - d * y ^ 2| = (p : ℤ) ^ l}

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

/-- **Rational solutions of the bisector equation for square-free $d > 1$.** Let $d > 1$ be a
square-free integer and let $a, b, c$ be rational numbers with $|a| \ne |b|$ and
$$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1).$$
Suppose there are rational numbers $u, v$ with $a^2 - d u^2 = -1$ and $b^2 - d v^2 = -1$. Then
there are rational numbers $a_2, b_2$ with $a^2 - d a_2^2 = -1$ and $b^2 - d b_2^2 = -1$ such
that either $a_2 + b_2 \ne 0$ and $c = (a b_2 + a_2 b) / (a_2 + b_2)$, or $a b_2 + a_2 b \ne 0$
and $c = -(a_2 + b_2) / (a b_2 + a_2 b)$.

In terms of $\alpha = a + a_2 \sqrt{d}$ and $\beta = b + b_2 \sqrt{d}$, which have norm $-1$, and
the conjugation $'$ of $\mathbb{Q}(\sqrt{d})$, the first quotient is
$(\alpha\beta - (\alpha\beta)') / (\alpha + \beta - (\alpha + \beta)')$.

Source: the theorem's second part (the factorization of $\alpha, \beta$ through $\eta$, $\xi_p$
and $S(d)$) is not formalized.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 1(ii), first
sentence (`integers-2024-A111-thm-1`). -/
public theorem_wanted bisector_equation_rat_solution_negPell (d : ℤ) (hd : 1 < d)
    (hsq : Squarefree d) (a b c : ℚ) (hab : |a| ≠ |b|)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1))
    (ha : ∃ a₂ : ℚ, a ^ 2 - d * a₂ ^ 2 = -1) (hb : ∃ b₂ : ℚ, b ^ 2 - d * b₂ ^ 2 = -1) :
    ∃ a₂ b₂ : ℚ, a ^ 2 - d * a₂ ^ 2 = -1 ∧ b ^ 2 - d * b₂ ^ 2 = -1 ∧
      ((a₂ + b₂ ≠ 0 ∧ c = (a * b₂ + a₂ * b) / (a₂ + b₂)) ∨
        (a * b₂ + a₂ * b ≠ 0 ∧ c = -(a₂ + b₂) / (a * b₂ + a₂ * b)))

/-- **Bisector-equation solutions from two solutions of $x^2 - d y^2 = -1$.** Let $d$ be an integer
and let $a, a_2, b, b_2$ be rational numbers with $a^2 - d a_2^2 = -1$ and $b^2 - d b_2^2 = -1$.
If $a_2 + b_2 \ne 0$, then $c = (a b_2 + a_2 b) / (a_2 + b_2)$ satisfies
$$(a - c)^2 (b^2 + 1) = (b - c)^2 (a^2 + 1),$$
and if $a b_2 + a_2 b \ne 0$, then $c = -(a_2 + b_2) / (a b_2 + a_2 b)$ satisfies it as well.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 1, converse
for (3) (`integers-2024-A111-thm-1`). -/
public theorem_wanted bisector_equation_form_three (d : ℤ) (a a₂ b b₂ : ℚ)
    (ha : a ^ 2 - d * a₂ ^ 2 = -1) (hb : b ^ 2 - d * b₂ ^ 2 = -1) :
    (a₂ + b₂ ≠ 0 → let c := (a * b₂ + a₂ * b) / (a₂ + b₂)
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) ∧
    (a * b₂ + a₂ * b ≠ 0 → let c := -(a₂ + b₂) / (a * b₂ + a₂ * b)
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1))

/-- **Products of strictly primitive solutions.** Let $d > 1$ be a square-free integer. Write
elements of $\mathbb{Z}[\sqrt{d}]$ as $u + v\sqrt{d}$ with integers $u, v$, and let
$N(u + v\sqrt{d}) = u^2 - d v^2$ be the norm. Let $p_1, \dots, p_r$ be distinct primes and
$n_1, \dots, n_r$ natural numbers, and suppose that each $a_i = u_i + v_i\sqrt{d}$ satisfies
$|N(a_i)| = p_i^{n_i}$ with $u_i$ and $d v_i$ coprime. Then $a = a_1 \cdots a_r = u + v\sqrt{d}$
satisfies $|N(a)| = p_1^{n_1} \cdots p_r^{n_r}$ with $u$ and $d v$ coprime; that is, $a$ gives a
strictly primitive solution of $|x^2 - d y^2| = p_1^{n_1} \cdots p_r^{n_r}$.

The sign $\pm$ in the source's equation (13) is dropped; negation preserves both conclusions.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 3(a)
(`integers-2024-A111-prop-3`). -/
public theorem_wanted strictlyPrimitive_prod (d : ℤ) (hd : 1 < d) (hsq : Squarefree d) {r : ℕ}
    (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (n : Fin r → ℕ)
    (a : Fin r → ℤ√d) (ha : ∀ i, IsCoprime (a i).re (d * (a i).im))
    (hN : ∀ i, |(a i).norm| = (p i : ℤ) ^ n i) :
    IsCoprime (∏ i, a i).re (d * (∏ i, a i).im) ∧ |(∏ i, a i).norm| = ∏ i, (p i : ℤ) ^ n i

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

/-- **Negating the value of a strictly primitive solution.** Let $d > 1$ be a square-free integer
such that $x^2 - d y^2 = -1$ has an integral solution, and let $z \ne 0$ be an integer. If
$x^2 - d y^2 = z$ has an integral solution with $x$ and $d y$ coprime, then so does
$x^2 - d y^2 = -z$.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 4
(`integers-2024-A111-prop-4`). -/
public theorem_wanted strictlyPrimitive_neg (d : ℤ) (hd : 1 < d) (hsq : Squarefree d) (z : ℤ)
    (hz : z ≠ 0) (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1)
    (h : ∃ x y : ℤ, IsCoprime x (d * y) ∧ x ^ 2 - d * y ^ 2 = z) :
    ∃ x y : ℤ, IsCoprime x (d * y) ∧ x ^ 2 - d * y ^ 2 = -z

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
      {p : ℕ | p.Prime ∧ ((Ideal.span {(p : ℤ)}).primesOver (NumberField.RingOfIntegers K)).ncard = 2}

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
      {p : ℕ | p.Prime ∧ ((Ideal.span {(p : ℤ)}).primesOver (NumberField.RingOfIntegers K)).ncard = 2}

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
