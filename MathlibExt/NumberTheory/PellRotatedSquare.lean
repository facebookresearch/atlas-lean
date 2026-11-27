/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Pell

/-!
# Integer solutions of the Pell equation in a closed rotated square region

If `a` is a fundamental solution of `x² - D y² = 1`, the coordinates of its natural powers
give all integer solutions by independent changes of sign. The functions `pellU` and `pellV`
interpolate these coordinates and appear in the shifted norm.

The statements follow Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell
Equation in a Closed Rotated Square Region*, INTEGERS 25 (2025), Article A112.
See also [the authors' preprint](https://arxiv.org/abs/2509.17882).
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
public theorem pell_solutions_eq_signed_powers {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) (x y : ℤ) :
    x ^ 2 - D * y ^ 2 = 1 ↔
      ∃ n : ℕ, ∃ i j : ℤ, (i = 1 ∨ i = -1) ∧ (j = 1 ∨ j = -1) ∧
        x = i * (a ^ n).x ∧ y = j * (a ^ n).y := by
  constructor
  · intro h
    let b : Pell.Solution₁ D := .mk |x| |y| (by simpa only [sq_abs] using h)
    have hx : x ≠ 0 := (Pell.Solution₁.mk x y h).x_ne_zero ha.d_pos.le
    obtain ⟨n, hn⟩ := ha.eq_pow_of_nonneg (a := b) (abs_pos.mpr hx) (abs_nonneg y)
    have signedAbs (z : ℤ) : ∃ i : ℤ, (i = 1 ∨ i = -1) ∧ z = i * |z| := by
      rcases abs_choice z with hz | hz
      · exact ⟨1, Or.inl rfl, by simp [hz]⟩
      · exact ⟨-1, Or.inr rfl, by simp [hz]⟩
    obtain ⟨i, hi, hix⟩ := signedAbs x
    obtain ⟨j, hj, hjy⟩ := signedAbs y
    exact ⟨n, i, j, hi, hj, hn ▸ hix, hn ▸ hjy⟩
  · rintro ⟨n, i, j, rfl | rfl, rfl | rfl, rfl, rfl⟩ <;> simpa using (a ^ n).prop

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

end

end MetaMathlibExt
