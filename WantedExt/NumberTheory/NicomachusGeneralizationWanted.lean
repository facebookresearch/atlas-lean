/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A balanced three or more-term generalization of Nicomachus' identity

Statements from Seon-Hong Kim and Kenneth B. Stolarsky,
"A Balanced Three or More-term Generalization of Nicomachus'
Identity", *INTEGERS* 26 (2026), Article A98
(<https://math.colgate.edu/~integers/aa98/aa98.pdf>).

Here `Tₘ = m(m+1)/2` is the `m`-th triangular number.  Theorem 1
gives two polynomial identities (7) and (8).  In (7) the summand of
`P_{m,o}` is `(4j + 1 + jx)·((j+1)(j-2) + j²x)`; this grouping,
ambiguous in plain-text extraction of the paper, is the one
satisfying (7) (verified by exact rational computation).
`P_{m,e}` in (8) is defined in the paper by substituting `-m - 1`
for `m` in the polynomial expansion of `P_{m,o}`; the expansion
used here is the Faulhaber expansion
`P_{m,o}(x) = Σ_p c_p(x) S_p(m)` with
`(c₀, c₁, c₂, c₃) = (-2, -9 - 2x, -3, 4 + 5x + x²)` and
`S_p(m) = Σ_{j=0}^m j^p`, which agrees with the defining sum for
natural `m` (again verified by exact rational computation).

The numbers `α_k` of Equation (12) are the continued-fraction
convergents `[1; 6, 3, …, 6, 3]` with `2k - 2` partial quotients
after the semicolon, so `α₁ = 1`; they are defined here by the
equivalent recurrence (13) from the paper,
`α_{k+1} = (15 + 7α_k)/(13 + 6α_k)`.

The integers `u_k` are the coefficients in Proposition 1: `u_k` is
the coefficient of `x^{k-1}` in
`(1 + 502x + x²)/((1 - x)(1 - 398x + x²))`, defined here directly
as a formal power series coefficient over `ℚ`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.NicomachusGeneralizationWanted

/-- **Triangular numbers as reals.** For a natural number $m$, $T_m = m(m+1)/2$ is the $m$-th
triangular number, viewed as a real number. -/
noncomputable def nicomachusTriangular (m : ℕ) : ℝ := (m : ℝ) * ((m : ℝ) + 1) / 2

/-- **The odd-case cube sum $L_{m,o}$.** For a natural number $m$ and a real number $x$,
$$L_{m,o}(x) = \sum_{j=1}^{m} (2j - 1)^3 + x^3 +
\sum_{j=2}^{m} \bigl((2j - 2) + (j - 1)x\bigr)^3.$$ -/
def nicomachusLOdd (m : ℕ) (x : ℝ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 m, (2 * (j : ℝ) - 1) ^ 3) + x ^ 3 +
    ∑ j ∈ Finset.Icc 2 m, ((2 * (j : ℝ) - 2) + ((j : ℝ) - 1) * x) ^ 3

/-- **The odd-case square $R_{m,o}(x)$.** For a natural number $m$ and a real number $x$,
$$R_{m,o}(x) = \bigl(T_{2m-1} + (1 + T_{m-1})\,x\bigr)^2,$$
where $T_n = n(n+1)/2$ is the $n$-th triangular number (for $m = 0$ the indices $2m - 1$ and
$m - 1$ are read as $0$). -/
noncomputable def nicomachusROdd (m : ℕ) (x : ℝ) : ℝ :=
  (nicomachusTriangular (2 * m - 1) +
    (1 + nicomachusTriangular (m - 1)) * x) ^ 2

/-- **The odd-case polynomial $P_{m,o}$.** For a natural number $m$ and a real number $x$,
$$P_{m,o}(x) = \sum_{j=0}^{m} (4j + 1 + jx) \bigl((j + 1)(j - 2) + j^2 x\bigr).$$ -/
def nicomachusPOdd (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 0 m,
    (4 * (j : ℝ) + 1 + (j : ℝ) * x) *
      (((j : ℝ) + 1) * ((j : ℝ) - 2) + (j : ℝ) ^ 2 * x)

/-- **The even-case cube sum $L_{m,e}$.** For a natural number $m$ and a real number $x$,
$$L_{m,e}(x) = \sum_{j=1}^{m} (2j - 1)^3 + x^3 + \sum_{j=1}^{m} (2j + jx)^3.$$ -/
def nicomachusLEven (m : ℕ) (x : ℝ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 m, (2 * (j : ℝ) - 1) ^ 3) + x ^ 3 +
    ∑ j ∈ Finset.Icc 1 m, (2 * (j : ℝ) + (j : ℝ) * x) ^ 3

/-- **The even-case square $R_{m,e}$.** For a natural number $m$ and a real number $x$,
$$R_{m,e}(x) = \bigl(T_{2m} + (1 + T_m)\,x\bigr)^2,$$
where $T_n = n(n+1)/2$ is the $n$-th triangular number. -/
noncomputable def nicomachusREven (m : ℕ) (x : ℝ) : ℝ :=
  (nicomachusTriangular (2 * m) +
    (1 + nicomachusTriangular m) * x) ^ 2

/-- **Faulhaber expansion of the odd-case polynomial.** For real numbers $m$ and $x$, let
$$\widetilde{P}(m, x) = -2(m + 1) - (9 + 2x) \, \frac{m(m+1)}{2} - 3 \cdot \frac{m(m+1)(2m+1)}{6} +
(4 + 5x + x^2) \left(\frac{m(m+1)}{2}\right)^2.$$

This is the polynomial in $m$ obtained from the sum defining the odd-case polynomial
$P_{m,o}(x)$ by the Faulhaber formulas for $\sum_{j=0}^{m} j^p$ with $p \le 3$; it agrees with
$P_{m,o}(x)$ at every natural number $m$. -/
noncomputable def nicomachusPClosed (m x : ℝ) : ℝ :=
  (-2) * (m + 1) + (-9 - 2 * x) * (m * (m + 1) / 2) +
    (-3) * (m * (m + 1) * (2 * m + 1) / 6) +
      (4 + 5 * x + x ^ 2) * (m * (m + 1) / 2) ^ 2

/-- **The even-case polynomial $P_{m,e}$.** For a natural number $m$ and a real number $x$,
$P_{m,e}(x) = \widetilde{P}(-m - 1, x)$, where $\widetilde{P}(m, x)$ is the Faulhaber expansion
of the odd-case polynomial $P_{m,o}(x)$ as a polynomial in $m$ (the paper defines $P_{m,e}(x)$
by substituting $-m - 1$ for $m$ in that expansion). -/
noncomputable def nicomachusPEven (m : ℕ) (x : ℝ) : ℝ :=
  nicomachusPClosed (-(m : ℝ) - 1) x

/-- **The Kim–Stolarsky convergents $\alpha_k$.** The rational numbers $\alpha_k$, for natural
numbers $k$, are defined by $\alpha_0 = 0$, $\alpha_1 = 1$ and
$\alpha_{k+1} = \frac{15 + 7\alpha_k}{13 + 6\alpha_k}$ for $k \ge 1$.

For $k \ge 1$, $\alpha_k$ is the continued-fraction convergent $[1; 6, 3, \ldots, 6, 3]$ with
$2k - 2$ partial quotients after the semicolon (Equation (12) of Kim and Stolarsky); the value
$\alpha_0 = 0$ is a placeholder. -/
def nicomachusAlpha : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (k + 2) => (15 + 7 * nicomachusAlpha (k + 1)) /
      (13 + 6 * nicomachusAlpha (k + 1))

/-- **The Kim–Stolarsky integers $u_k$.** For a natural number $k$, $u_k$ is the coefficient of
$x^{k-1}$ in the power series expansion over $\mathbb{Q}$ of
$$\frac{1 + 502x + x^2}{(1 - x)(1 - 398x + x^2)}.$$
For $k \ge 1$ these are the integers $u_k$ of Proposition 1 of Kim and Stolarsky; for $k = 0$ the
exponent $k - 1$ is read as $0$, so $u_0 = u_1 = 1$. -/
noncomputable def nicomachusU (k : ℕ) : ℚ :=
  PowerSeries.coeff (k - 1)
    ((1 + 502 * PowerSeries.X + PowerSeries.X ^ 2) *
      ((1 - PowerSeries.X) *
        (1 - 398 * PowerSeries.X + PowerSeries.X ^ 2))⁻¹)

/-- **Generalized Nicomachus identity, odd case.** Let $L_{m,o}$ be the odd-case cube sum,
$R_{m,o}$ the odd-case square and $P_{m,o}$ the odd-case polynomial. For every natural number
$m \ge 2$ and every real number $x$,
$$L_{m+1,o}(x) - R_{m+1,o}(x) = x \, P_{m,o}(x) - x^2 + x^3.$$

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Theorem 1. -/
theorem_wanted nicomachusLOdd_sub_ROdd_succ_eq (m : ℕ) (hm : 2 ≤ m)
    (x : ℝ) :
    nicomachusLOdd (m + 1) x - nicomachusROdd (m + 1) x =
      x * nicomachusPOdd m x - x ^ 2 + x ^ 3

/-- **Generalized Nicomachus identity, even case.** Let $L_{m,e}$ be the even-case cube sum,
$R_{m,e}$ the even-case square and $P_{m,e}$ the even-case polynomial. For every natural number
$m \ge 2$ and every real number $x$,
$$L_{m,e}(x) - R_{m,e}(x) = x \, P_{m,e}(x) - x^2 + x^3.$$

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Theorem 1. -/
theorem_wanted nicomachusLEven_sub_REven_eq (m : ℕ) (hm : 2 ≤ m)
    (x : ℝ) :
    nicomachusLEven m x - nicomachusREven m x =
      x * nicomachusPEven m x - x ^ 2 + x ^ 3

/-- **Closed form for the Kim–Stolarsky integers $u_k$.** Let $u_k$ be the coefficient of
$x^{k-1}$ in the power series expansion of $(1 + 502x + x^2)/((1 - x)(1 - 398x + x^2))$. For every
integer $k \ge 1$,
$$u_k = \frac{5(10 - 3\sqrt{11})^{2k-1} + 5(10 + 3\sqrt{11})^{2k-1} - 56}{44}.$$

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Proposition 1. -/
theorem_wanted nicomachusU_eq_closedForm (k : ℕ) (hk : 1 ≤ k) :
    (nicomachusU k : ℝ) =
      (5 * (10 - 3 * Real.sqrt 11) ^ (2 * k - 1) +
        5 * (10 + 3 * Real.sqrt 11) ^ (2 * k - 1) - 56) / 44

/-- **Recurrence for the Kim–Stolarsky integers $u_k$.** Let $u_k$ be the coefficient of
$x^{k-1}$ in the power series expansion of $(1 + 502x + x^2)/((1 - x)(1 - 398x + x^2))$. For every
integer $k \ge 1$,
$$u_{k+1} = 252 + 199u_k + 30\sqrt{(3 + 2u_k)(23 + 22u_k)}.$$

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Proposition 1. -/
theorem_wanted nicomachusU_succ_eq (k : ℕ) (hk : 1 ≤ k) :
    (nicomachusU (k + 1) : ℝ) =
      252 + 199 * (nicomachusU k : ℝ) +
        30 * Real.sqrt ((3 + 2 * (nicomachusU k : ℝ)) *
          (23 + 22 * (nicomachusU k : ℝ)))

/-- **The convergents $\alpha_k$ in terms of the integers $u_k$.** Let $\alpha_k$ be the
Kim–Stolarsky convergents, with $\alpha_1 = 1$ and
$\alpha_{k+1} = (15 + 7\alpha_k)/(13 + 6\alpha_k)$ for $k \ge 1$, and let $u_k$ be the
coefficient of $x^{k-1}$ in the power series expansion of
$(1 + 502x + x^2)/((1 - x)(1 - 398x + x^2))$. For every integer $k \ge 1$,
$$\alpha_k = \frac{-1 + \sqrt{11 - \frac{10}{3 + 2u_k}}}{2}.$$

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Proposition 2. -/
theorem_wanted nicomachusAlpha_eq (k : ℕ) (hk : 1 ≤ k) :
    (nicomachusAlpha k : ℝ) =
      (-1 + Real.sqrt (11 - 10 / (3 + 2 * (nicomachusU k : ℝ)))) / 2

/-- **Kim–Stolarsky balanced quadratic sum.** Let $k \ge 1$, let $\alpha_k$ be the numbers of
Equation (12) (so $\alpha_1 = 1$ and $\alpha_{k+1} = (15 + 7\alpha_k)/(13 + 6\alpha_k)$), let $u_k$
be the integers of Proposition 1, and let $T_n = n(n+1)/2$. With
$(a, b, c) = (1, \alpha_k, -(1 + \alpha_k))$ and $(d, e, f) = (-a, -c, -b)$ as in (17), for every
natural number $m$,
$$\sum_{j=1}^{m} (a + bj + cj^2)(d + ej + fj^2) =
T_{m-1}\left(\frac{(1 + m)(2 - 3m^2)}{3(3 + 2u_k)} + (3 + 2m)\,T_{m-1}\right).$$

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Theorem 2. -/
theorem_wanted sum_quadratic_mul_quadratic_eq (k : ℕ) (hk : 1 ≤ k)
    (m : ℕ) :
    (∑ j ∈ Finset.Icc 1 m,
      (1 + (nicomachusAlpha k : ℝ) * (j : ℝ) -
          (1 + (nicomachusAlpha k : ℝ)) * (j : ℝ) ^ 2) *
        (-1 + (1 + (nicomachusAlpha k : ℝ)) * (j : ℝ) -
          (nicomachusAlpha k : ℝ) * (j : ℝ) ^ 2)) =
      nicomachusTriangular (m - 1) *
        (((1 + (m : ℝ)) * (2 - 3 * (m : ℝ) ^ 2) /
          (3 * (3 + 2 * (nicomachusU k : ℝ)))) +
            (3 + 2 * (m : ℝ)) * nicomachusTriangular (m - 1))

end MathlibExt.NumberTheory.NicomachusGeneralizationWanted
