/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Pell

/-!
# Integer solutions of the Pell equation in a closed rotated square region

Statements from Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in
a Closed Rotated Square Region*, INTEGERS 25 (2025), Article A112.

For a positive nonsquare integer `D`, the fundamental solution `(α, β)` of `x² - D y² = 1` is
the coordinates of a Mathlib fundamental solution `a : Pell.Solution₁ D` (`Pell.IsFundamental a`,
which forces `0 < D` and `D` nonsquare), and `u_n + v_n √D = (α + β √D)^n` are the coordinates of
`a ^ n`. The real interpolations `u(x)` and `v(x)` of (1.3)-(1.4) are `pellU` and `pellV`; both
bases `α ± β √D` are positive, so real powers are used.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The Pell interpolation function u.** For integers $D$, $\alpha$, $\beta$, the function
$u : \mathbb{R} \to \mathbb{R}$ is
$u(x) = ((\alpha + \beta\sqrt D)^x + (\alpha - \beta\sqrt D)^x)/2$, where $\sqrt D$ is the real
square root (zero when $D < 0$) and $(\cdot)^x$ is the real power.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Section 1, Equation (1.3). -/
public noncomputable def pellU (D α β : ℤ) (x : ℝ) : ℝ :=
  ((α + β * Real.sqrt D) ^ x + (α - β * Real.sqrt D) ^ x) / 2

/-- **The Pell interpolation function v.** For integers $D$, $\alpha$, $\beta$, the function
$v : \mathbb{R} \to \mathbb{R}$ is
$v(x) = ((\alpha + \beta\sqrt D)^x - (\alpha - \beta\sqrt D)^x)/(2\sqrt D)$, where $\sqrt D$ is the
real square root (zero when $D < 0$), $(\cdot)^x$ is the real power and division by zero gives
$0$; in particular $v$ is identically $0$ when $D \le 0$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Section 1, Equation (1.4). -/
public noncomputable def pellV (D α β : ℤ) (x : ℝ) : ℝ :=
  ((α + β * Real.sqrt D) ^ x - (α - β * Real.sqrt D) ^ x) / (2 * Real.sqrt D)

/-- **Value of the Pell interpolation function u at 0.** For all integers $D$, $\alpha$, $\beta$,
the function $u(x) = ((\alpha + \beta\sqrt D)^x + (\alpha - \beta\sqrt D)^x)/2$ of a real
variable $x$ satisfies $u(0) = 1$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Section 1, Equation (1.3). -/
public theorem pellU_zero (D α β : ℤ) : pellU D α β 0 = 1 := by
  norm_num [pellU]

/-- **Value of the Pell interpolation function v at 0.** For all integers $D$, $\alpha$, $\beta$,
the function $v(x) = ((\alpha + \beta\sqrt D)^x - (\alpha - \beta\sqrt D)^x)/(2\sqrt D)$ of a real
variable $x$, where $\sqrt D$ is the real square root (zero when $D < 0$) and division by zero
gives $0$, satisfies $v(0) = 0$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Section 1, Equation (1.4). -/
public theorem pellV_zero (D α β : ℤ) : pellV D α β 0 = 0 := by
  norm_num [pellV]

/-- **Pell solutions are signed powers of the fundamental solution.** Let $D$ be an integer and
let $(\alpha, \beta)$ be a fundamental solution of $x^2 - Dy^2 = 1$, that is, an integer solution
with $\alpha > 1$ and $\beta > 0$ such that $\alpha \le x$ for every integer solution $(x, y)$ with
$x > 1$ (one exists only when $D$ is positive and not a square). For $n \ge 0$ let $u_n, v_n$ be
the integers with $u_n + v_n\sqrt D = (\alpha + \beta\sqrt D)^n$. Then integers $x, y$ satisfy
$x^2 - Dy^2 = 1$ if and only if $x = i\,u_n$ and $y = j\,v_n$ for some integer $n \ge 0$ and some
signs $i, j \in \{1, -1\}$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Proposition 1.1
(`integers-2025-A112-prop-1-1`). -/
public theorem_wanted pell_solutions_eq_signed_powers {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) (x y : ℤ) :
    x ^ 2 - D * y ^ 2 = 1 ↔
      ∃ n : ℕ, ∃ i j : ℤ, (i = 1 ∨ i = -1) ∧ (j = 1 ∨ j = -1) ∧
        x = i * (a ^ n).x ∧ y = j * (a ^ n).y

/-- **The Pell interpolation functions agree with the solution sequence at natural numbers.** Let
$D$ be an integer and let $(\alpha, \beta)$ be a fundamental solution of $x^2 - Dy^2 = 1$, that
is, an integer solution with $\alpha > 1$ and $\beta > 0$ such that $\alpha \le x$ for every
integer solution $(x, y)$ with $x > 1$ (one exists only when $D$ is positive and not a square).
For $n \ge 0$ let $u_n, v_n$ be the integers with $u_n + v_n\sqrt D = (\alpha + \beta\sqrt D)^n$,
and for real $t$ let $u(t) = ((\alpha + \beta\sqrt D)^t + (\alpha - \beta\sqrt D)^t)/2$ and
$v(t) = ((\alpha + \beta\sqrt D)^t - (\alpha - \beta\sqrt D)^t)/(2\sqrt D)$. Then $u(n) = u_n$ and
$v(n) = v_n$ for every natural number $n$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Proposition 1.2
(`integers-2025-A112-prop-1-2`). -/
public theorem_wanted pellU_pellV_natCast {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) (n : ℕ) :
    pellU D a.x a.y n = (a ^ n).x ∧ pellV D a.x a.y n = (a ^ n).y

/-- **Closed form for inverting the sum of the Pell interpolating functions.** Let $D$ be an
integer, let $(\alpha, \beta)$ be the fundamental solution of the Pell equation $X^2 - D Y^2 = 1$,
put $\varepsilon = \alpha + \beta \sqrt{D}$ and $\bar\varepsilon = \alpha - \beta \sqrt{D}$, and let
$u(t) = (\varepsilon^t + \bar\varepsilon^t) / 2$ and
$v(t) = (\varepsilon^t - \bar\varepsilon^t) / (2 \sqrt{D})$ for real $t$. For every real $x \ge 1$,
put $z = (D x - \sqrt{D x^2 - D + 1}) / (D - 1)$ and
$g = \log(z + \sqrt{z^2 - 1}) / \log \varepsilon$. Then $g \ge 0$ and $u(g) + v(g) = x$.

Here $\log(z + \sqrt{z^2 - 1})$ is $\cosh^{-1}(z)$ written in logarithmic form.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Theorem 2.2, Equation (2.1)
(`integers-2025-A112-thm-2-2`). -/
public theorem_wanted pell_inverse_closed_form {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) {x : ℝ} (hx : 1 ≤ x) :
    let z : ℝ := (D * x - Real.sqrt (D * x ^ 2 - D + 1)) / (D - 1)
    let g : ℝ := Real.log (z + Real.sqrt (z ^ 2 - 1)) / Real.log (a.x + a.y * Real.sqrt D)
    0 ≤ g ∧ pellU D a.x a.y g + pellV D a.x a.y g = x

/-- **Floor of the inverse of the sum of the Pell interpolating functions.** Let $D$ be an
integer, let $(\alpha, \beta)$ be the fundamental solution of the Pell equation $X^2 - D Y^2 = 1$,
put $\varepsilon = \alpha + \beta \sqrt{D}$ and $\bar\varepsilon = \alpha - \beta \sqrt{D}$, and let
$u(s) = (\varepsilon^s + \bar\varepsilon^s) / 2$ and
$v(s) = (\varepsilon^s - \bar\varepsilon^s) / (2 \sqrt{D})$ for real $s$. If $x \ge 1$ and $t \ge 0$
are real numbers with $u(t) + v(t) = x$, then
$\lfloor t \rfloor = \lfloor (\log \lfloor x \rfloor + C) / \log \varepsilon \rfloor$, where
$C = \log(2 \sqrt{D} / (1 + \sqrt{D}))$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Theorem 2.3, Equation (2.5)
(`integers-2025-A112-thm-2-3`). -/
public theorem_wanted pell_inverse_floor {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) {x t : ℝ} (hx : 1 ≤ x) (ht : 0 ≤ t)
    (htx : pellU D a.x a.y t + pellV D a.x a.y t = x) :
    ⌊t⌋ = ⌊(Real.log (⌊x⌋ : ℝ) + Real.log (2 * Real.sqrt D / (1 + Real.sqrt D))) /
      Real.log (a.x + a.y * Real.sqrt D)⌋

/-- **Pell solutions in a closed rotated square.** Let $D$ be an integer and let $(\alpha, \beta)$
be a fundamental solution of $x^2 - Dy^2 = 1$, that is, an integer solution with $\alpha > 1$
and $\beta > 0$ such that $\alpha \le x$ for every integer solution $(x, y)$ with $x > 1$ (one
exists only when $D$ is positive and not a square). For $n \ge 0$ let $u_n, v_n$ be the
integers with $u_n + v_n\sqrt D = (\alpha + \beta\sqrt D)^n$, and for real $t$ let
$u(t) = ((\alpha + \beta\sqrt D)^t + (\alpha - \beta\sqrt D)^t)/2$ and
$v(t) = ((\alpha + \beta\sqrt D)^t - (\alpha - \beta\sqrt D)^t)/(2\sqrt D)$. For real $\lambda$
let $Q(\lambda)$ be the set of integer pairs $(x, y)$ with $x^2 - Dy^2 = 1$ and
$|x| + |y| \le \lambda$. If $\lambda < 1$, then $Q(\lambda)$ is empty. If $\lambda \ge 1$, then
for every real $t \ge 0$ with $u(t) + v(t) = \lambda$, the set $Q(\lambda)$ consists of the pairs
$(i\,u_n, j\,v_n)$ with $i, j \in \{1, -1\}$ and integers $0 \le n \le t$, and it has exactly
$2 + 4\lfloor t \rfloor$ elements.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Theorem 2.1
(`integers-2025-A112-thm-2-1`). -/
public theorem_wanted pell_solutions_in_rotated_square {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) (lam : ℝ) :
    let Q : Set (ℤ × ℤ) := {p | p.1 ^ 2 - D * p.2 ^ 2 = 1 ∧ ((|p.1| + |p.2| : ℤ) : ℝ) ≤ lam}
    (lam < 1 → Q = ∅) ∧
    ∀ t : ℝ, 1 ≤ lam → 0 ≤ t → pellU D a.x a.y t + pellV D a.x a.y t = lam →
      Q = {p | ∃ n : ℕ, (n : ℝ) ≤ t ∧ ∃ i j : ℤ, (i = 1 ∨ i = -1) ∧ (j = 1 ∨ j = -1) ∧
        p = (i * (a ^ n).x, j * (a ^ n).y)} ∧
      Q.ncard = 2 + 4 * ⌊t⌋₊

/-- **Explicit count of Pell solutions in a closed rotated square.** Let $D$ be an integer and let
$(\alpha, \beta)$ be a fundamental solution of $x^2 - Dy^2 = 1$, that is, an integer solution
with $\alpha > 1$ and $\beta > 0$ such that $\alpha \le x$ for every integer solution $(x, y)$ with
$x > 1$ (one exists only when $D$ is positive and not a square). For $n \ge 0$ let $u_n, v_n$ be
the integers with $u_n + v_n\sqrt D = (\alpha + \beta\sqrt D)^n$. For real $\lambda$ let
$Q(\lambda)$ be the set of integer pairs $(x, y)$ with $x^2 - Dy^2 = 1$ and
$|x| + |y| \le \lambda$. If $\lambda < 1$, then $Q(\lambda)$ is empty. If $\lambda \ge 1$, let
$m = \left\lfloor \left(\log\lfloor\lambda\rfloor + \log\frac{2\sqrt D}{1 + \sqrt D}\right) /
\log(\alpha + \beta\sqrt D) \right\rfloor$; then $Q(\lambda)$ consists of the pairs
$(i\,u_n, j\,v_n)$ with $i, j \in \{1, -1\}$ and integers $0 \le n \le m$, and $Q(\lambda)$ has
exactly $2 + 4m$ elements.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Corollary 2.4
(`integers-2025-A112-cor-2-4`). -/
public theorem_wanted pell_solutions_in_rotated_square_explicit {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) (lam : ℝ) :
    let Q : Set (ℤ × ℤ) := {p | p.1 ^ 2 - D * p.2 ^ 2 = 1 ∧ ((|p.1| + |p.2| : ℤ) : ℝ) ≤ lam}
    let m : ℤ := ⌊(Real.log (⌊lam⌋ : ℝ) + Real.log (2 * Real.sqrt D / (1 + Real.sqrt D))) /
      Real.log (a.x + a.y * Real.sqrt D)⌋
    (lam < 1 → Q = ∅) ∧
    (1 ≤ lam →
      Q = {p | ∃ n : ℕ, (n : ℤ) ≤ m ∧ ∃ i j : ℤ, (i = 1 ∨ i = -1) ∧ (j = 1 ∨ j = -1) ∧
        p = (i * (a ^ n).x, j * (a ^ n).y)} ∧
      (Q.ncard : ℤ) = 2 + 4 * m)

/-- **Shifted real Pell solutions eventually lie in the closed quadrants.** Let $D$ be an integer
and let $(\alpha, \beta)$ be a fundamental solution of $X^2 - DY^2 = 1$, that is, an integer
solution with $\alpha > 1$ and $\beta > 0$ such that $\alpha \le X$ for every integer solution
$(X, Y)$ with $X > 1$ (one exists only when $D$ is positive and not a square). For real $x$ let
$u(x) = ((\alpha + \beta\sqrt D)^x + (\alpha - \beta\sqrt D)^x)/2$ and
$v(x) = ((\alpha + \beta\sqrt D)^x - (\alpha - \beta\sqrt D)^x)/(2\sqrt D)$, and for integers $a$,
$b$ and signs $i, j \in \{1, -1\}$ let $R_{i,j}(x) = (i\,u(x) + a, j\,v(x) + b)$. Then there is a
real $x_0$ such that for every real $x \ge x_0$ the point $R_{1,1}(x)$ lies in the closed first
quadrant $\{X \ge 0, Y \ge 0\}$, $R_{-1,1}(x)$ in the closed second quadrant
$\{X \le 0, Y \ge 0\}$, $R_{-1,-1}(x)$ in the closed third quadrant $\{X \le 0, Y \le 0\}$ and
$R_{1,-1}(x)$ in the closed fourth quadrant $\{X \ge 0, Y \le 0\}$.

The points $R_{i,j}(x)$ are real solutions of the shifted Pell equation
$(X - a)^2 - D(Y - b)^2 = 1$. The printed statement of the source swaps the third and fourth
quadrants; this statement follows the reading of the source's proof.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Proposition 3.1
(`integers-2025-A112-prop-3-1`). -/
public theorem_wanted pell_shifted_real_solutions_eventually_in_quadrants {D : ℤ}
    {w : Pell.Solution₁ D} (hw : Pell.IsFundamental w) (a b : ℤ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (0 ≤ pellU D w.x w.y x + a ∧ 0 ≤ pellV D w.x w.y x + b) ∧
      (-pellU D w.x w.y x + a ≤ 0 ∧ 0 ≤ pellV D w.x w.y x + b) ∧
      (-pellU D w.x w.y x + a ≤ 0 ∧ -pellV D w.x w.y x + b ≤ 0) ∧
      (0 ≤ pellU D w.x w.y x + a ∧ -pellV D w.x w.y x + b ≤ 0)

/-- **Largest intercept norm of a shifted Pell curve.** Let $D > 0$, $a \ne 0$ and $b$ be
integers. The intercepts of the shifted Pell curve $(x - a)^2 - D (y - b)^2 = 1$ with the axes
are $(a \pm \sqrt{1 + D b^2}, 0)$ and $(0, b \pm \sqrt{(a^2 - 1) / D})$, with $L^1$ norms
$|a \pm \sqrt{1 + D b^2}|$ and $|b \pm \sqrt{(a^2 - 1) / D}|$. The largest of these four norms
is $|a| + \sqrt{1 + D b^2}$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Proposition 3.2
(`integers-2025-A112-prop-3-2`). -/
public theorem_wanted pell_shifted_intercepts_max {D a : ℤ} (hD : 0 < D) (ha : a ≠ 0) (b : ℤ) :
    |(a : ℝ)| + Real.sqrt (1 + D * b ^ 2) =
      max (max |a + Real.sqrt (1 + D * b ^ 2)| |a - Real.sqrt (1 + D * b ^ 2)|)
        (max |b + Real.sqrt ((a ^ 2 - 1) / D)| |b - Real.sqrt ((a ^ 2 - 1) / D)|)

/-- **The $L^1$ norm along a shifted Pell curve.** For integers $D$, $\alpha$, $\beta$, $a$, $b$,
$i$ and $j$, put $\varepsilon = \alpha + \beta \sqrt{D}$ and
$\bar\varepsilon = \alpha - \beta \sqrt{D}$, and let
$u(x) = (\varepsilon^x + \bar\varepsilon^x) / 2$ and
$v(x) = (\varepsilon^x - \bar\varepsilon^x) / (2 \sqrt{D})$ for real $x$. The function $f_{i,j}$
is defined on the reals by $f_{i,j}(x) = |i u(x) + a| + |j v(x) + b|$.

No condition is placed on the integers: $\sqrt{s} = 0$ for $s < 0$, a quotient by $0$ is $0$, and
for real $c < 0$ the power $c^x$ means $|c|^x \cos(\pi x)$, while $0^0 = 1$ and $0^x = 0$ for
$x \ne 0$.

In the source, $(\alpha, \beta)$ is the fundamental solution of $X^2 - D Y^2 = 1$,
$i, j \in \{1, -1\}$, and $f_{i,j}(x)$ is the $L^1$ norm of the real solution
$R_{i,j}(x) = (i u(x) + a, j v(x) + b)$ of the shifted Pell equation
$(X - a)^2 - D (Y - b)^2 = 1$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Section 3, definition of `f_{i,j}`. -/
public noncomputable def pellShiftedNorm (D α β a b i j : ℤ) (x : ℝ) : ℝ :=
  |i * pellU D α β x + a| + |j * pellV D α β x + b|

/-- **Value at zero of the shifted Pell norm function.** Let $D$, $\alpha$, $\beta$, $a$, $b$,
$i$ and $j$ be integers. Put $\varepsilon = \alpha + \beta \sqrt{D}$ and
$\bar\varepsilon = \alpha - \beta \sqrt{D}$, let
$u(x) = (\varepsilon^x + \bar\varepsilon^x) / 2$ and
$v(x) = (\varepsilon^x - \bar\varepsilon^x) / (2 \sqrt{D})$ for real $x$, and let
$f_{i,j}(x) = |i u(x) + a| + |j v(x) + b|$. Then $f_{i,j}(0) = |i + a| + |b|$.

Here $\sqrt{s} = 0$ for $s < 0$, a quotient by $0$ is $0$, and $c^0 = 1$ for every real $c$; no
condition is placed on the integers.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Section 3, definition of `f_{i,j}`. -/
public theorem pellShiftedNorm_zero (D α β a b i j : ℤ) :
    pellShiftedNorm D α β a b i j 0 = |(i : ℝ) + a| + |(b : ℝ)| := by
  simp [pellShiftedNorm, pellU_zero, pellV_zero]

/-- **The bound $K$ for the shifted Pell equation.** For integers $D$, $a$ and $b$, the constant
attached to the shifted Pell equation $(x - a)^2 - D (y - b)^2 = 1$ is the real number
$K = |a| + \max(|b| + 1, \sqrt{1 + D b^2})$, where $\sqrt{s}$ is taken to be $0$ for $s < 0$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Theorem 3.3, definition of `K`. -/
public noncomputable def pellShiftBound (D a b : ℤ) : ℝ :=
  |(a : ℝ)| + max (|(b : ℝ)| + 1) (Real.sqrt (1 + D * b ^ 2))

/-- **The bound $K$ of the unshifted Pell equation.** For every integer $D$, the constant
$K = |a| + \max(|b| + 1, \sqrt{1 + D b^2})$ with $a = b = 0$ equals $1$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Theorem 3.3, definition of `K`. -/
public theorem pellShiftBound_zero_zero (D : ℤ) : pellShiftBound D 0 0 = 1 := by
  simp [pellShiftBound]

/-- **The shifted Pell norm function at zero is at most the bound.** Let $D$, $\alpha$, $\beta$,
$a$ and $b$ be integers and let $i, j \in \{1, -1\}$. Put $\varepsilon = \alpha + \beta \sqrt{D}$
and $\bar\varepsilon = \alpha - \beta \sqrt{D}$, let
$u(x) = (\varepsilon^x + \bar\varepsilon^x) / 2$ and
$v(x) = (\varepsilon^x - \bar\varepsilon^x) / (2 \sqrt{D})$ for real $x$, let
$f_{i,j}(x) = |i u(x) + a| + |j v(x) + b|$ and let $K = |a| + \max(|b| + 1, \sqrt{1 + D b^2})$.
Then $f_{i,j}(0) \le K$.

Here $\sqrt{s} = 0$ for $s < 0$, a quotient by $0$ is $0$, and $c^0 = 1$ for every real $c$; no
further condition is placed on the integers.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Lemma 3.5
(`integers-2025-A112-lem-3-5`). -/
public theorem_wanted pellShiftedNorm_zero_le_pellShiftBound (D α β a b : ℤ) {i j : ℤ}
    (hi : i = 1 ∨ i = -1) (hj : j = 1 ∨ j = -1) :
    pellShiftedNorm D α β a b i j 0 ≤ pellShiftBound D a b

/-- **The shifted Pell norm function is at most the bound up to its last crossing.** Let $D$ be
an integer, let $(\alpha, \beta)$ be the fundamental solution of the Pell equation
$X^2 - D Y^2 = 1$, put $\varepsilon = \alpha + \beta \sqrt{D}$ and
$\bar\varepsilon = \alpha - \beta \sqrt{D}$, and let
$u(x) = (\varepsilon^x + \bar\varepsilon^x) / 2$ and
$v(x) = (\varepsilon^x - \bar\varepsilon^x) / (2 \sqrt{D})$ for real $x$. Let $a$ and $b$ be
integers, let $i, j \in \{1, -1\}$, let $f_{i,j}(x) = |i u(x) + a| + |j v(x) + b|$, let
$K = |a| + \max(|b| + 1, \sqrt{1 + D b^2})$ and let $x_1 = \sup \{y \ge 0 : f_{i,j}(y) = K\}$.
Then $f_{i,j}(x) \le K$ for every real $x$ with $0 \le x \le x_1$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Lemma 3.6
(`integers-2025-A112-lem-3-6`). -/
public theorem_wanted pellShiftedNorm_le_pellShiftBound {D : ℤ} {w : Pell.Solution₁ D}
    (hw : Pell.IsFundamental w) (a b : ℤ) {i j : ℤ} (hi : i = 1 ∨ i = -1) (hj : j = 1 ∨ j = -1)
    {x : ℝ} (hx₀ : 0 ≤ x)
    (hx : x ≤ sSup {y : ℝ | 0 ≤ y ∧
      pellShiftedNorm D w.x w.y a b i j y = pellShiftBound D a b}) :
    pellShiftedNorm D w.x w.y a b i j x ≤ pellShiftBound D a b

/-- **The shifted Pell norm function is increasing past its last crossing of the bound.** Let $D$
be an integer, let $(\alpha, \beta)$ be the fundamental solution of the Pell equation
$X^2 - D Y^2 = 1$, put $\varepsilon = \alpha + \beta \sqrt{D}$ and
$\bar\varepsilon = \alpha - \beta \sqrt{D}$, and let
$u(x) = (\varepsilon^x + \bar\varepsilon^x) / 2$ and
$v(x) = (\varepsilon^x - \bar\varepsilon^x) / (2 \sqrt{D})$ for real $x$. Let $a$ and $b$ be
integers, let $i, j \in \{1, -1\}$, let $f_{i,j}(x) = |i u(x) + a| + |j v(x) + b|$, let
$K = |a| + \max(|b| + 1, \sqrt{1 + D b^2})$ and let $x_1 = \sup \{y \ge 0 : f_{i,j}(y) = K\}$.
Then $f_{i,j}(x) = u(x) + v(x) + i a + j b$ for every real $x \ge x_1$, the function $f_{i,j}$ is
strictly increasing on $[x_1, \infty)$, and $f_{i,j}$ maps $[x_1, \infty)$ bijectively onto
$[K, \infty)$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Lemma 3.7
(`integers-2025-A112-lem-3-7`). -/
public theorem_wanted pellShiftedNorm_bijOn_Ici {D : ℤ} {w : Pell.Solution₁ D}
    (hw : Pell.IsFundamental w) (a b : ℤ) {i j : ℤ} (hi : i = 1 ∨ i = -1) (hj : j = 1 ∨ j = -1) :
    let x₁ : ℝ := sSup {y : ℝ | 0 ≤ y ∧
      pellShiftedNorm D w.x w.y a b i j y = pellShiftBound D a b}
    (∀ x, x₁ ≤ x →
      pellShiftedNorm D w.x w.y a b i j x = pellU D w.x w.y x + pellV D w.x w.y x + i * a + j * b) ∧
    StrictMonoOn (pellShiftedNorm D w.x w.y a b i j) (Set.Ici x₁) ∧
    Set.BijOn (pellShiftedNorm D w.x w.y a b i j) (Set.Ici x₁) (Set.Ici (pellShiftBound D a b))

end

end MetaMathlibExt
