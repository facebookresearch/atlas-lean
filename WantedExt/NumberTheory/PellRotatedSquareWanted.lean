/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.PellInverseClosedForm
public import MathlibExt.NumberTheory.PellShiftedIntercepts
public import MathlibExt.NumberTheory.PellShiftedQuadrants

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
