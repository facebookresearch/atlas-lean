/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.Bernoulli

namespace MetaMathlibExt

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators Topology

/--
**Generalized Watson trigonometric sum.** For natural numbers $n$ and $\nu$, $C_n(\nu)$ is the real
number
$$
C_n(\nu) = \sum_{l=1}^{n-1} \frac{\cos(2\pi\nu l/n)}{\sin(\pi l/n)}.
$$
For $n \le 1$ the sum is empty and $C_n(\nu) = 0$.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, definition of `C_n(ν)`.
-/
public noncomputable def watsonCosSum (n ν : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 (n - 1),
    Real.cos (2 * Real.pi * (ν : ℝ) * (l : ℝ) / (n : ℝ)) *
      (1 / Real.sin (Real.pi * (l : ℝ) / (n : ℝ)))

/--
**Watson's alternating cosecant sum.** For a natural number $n$, the alternating cosecant sum is
the real number
$$
C_n = \sum_{l=1}^{n-1} \frac{(-1)^{l+1}}{\sin(\pi l / n)}.
$$
For $n \le 1$ the sum is empty and $C_n = 0$.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, definition of `C_n`.
-/
public noncomputable def watsonAlternatingCosecantSum (n : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 (n - 1),
    (-1 : ℝ) ^ (l + 1) * (1 / Real.sin (Real.pi * (l : ℝ) / (n : ℝ)))

/--
**Watson's cosine sum at $n = 2$, $\nu = 1$.** The cosine sum
$C_n(\nu) = \sum_{l=1}^{n-1} \cos(2 \pi \nu l / n) / \sin(\pi l / n)$ satisfies $C_2(1) = -1$.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, definition of `C_n(ν)`.
-/
public theorem watsonCosSum_two_one : watsonCosSum 2 1 = -1 := by
  norm_num [watsonCosSum, Real.sin_pi_div_two]

/--
**Watson's alternating cosecant sum at $n = 2$.** The alternating cosecant sum
$C_2 = \sum_{l=1}^{1} (-1)^{l+1} / \sin(\pi l / 2)$ equals $1$.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, definition of `C_n`.
-/
public theorem watsonAlternatingCosecantSum_two : watsonAlternatingCosecantSum 2 = 1 := by
  norm_num [watsonAlternatingCosecantSum, Real.sin_pi_div_two]

/--
**Odd cotangent derivatives.** For natural numbers $r$, $n$ and $\nu$, $\mathcal{H}_{2r-1}(\nu/n)$
is the real number $\cot^{(2r-1)}(\pi\nu/n)$, the $(2r-1)$st derivative of the cotangent function
evaluated at $\pi\nu/n$. Here $2r - 1$ is computed in the natural numbers, so for $r = 0$ this is
$\cot(\pi\nu/n)$ itself.

The derivative is taken of the cotangent as a function on all of $\mathbb{R}$; the value is the
classical one whenever $\pi\nu/n$ is not a multiple of $\pi$.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, definition of `ℋ_{2r-1}`.
-/
public noncomputable def watsonOddCotangentDeriv (r n ν : ℕ) : ℝ :=
  iteratedDeriv (2 * r - 1) Real.cot (Real.pi * (ν : ℝ) / (n : ℝ))

/--
**Digamma evaluation of a hyperbolic Laplace integral.** Let $b > 0$ be a real number and let
$\alpha, \beta$ be complex numbers with $\operatorname{Re}(\alpha + b - \beta) > 0$ and
$\operatorname{Re}(\alpha + b + \beta) > 0$. Then the function
$x \mapsto e^{-\alpha x} \cosh(\beta x) / \cosh(bx)$ is integrable on $(0, \infty)$, and, writing
$\psi$ for the digamma function,
$$
\int_0^\infty \frac{e^{-\alpha x} \cosh(\beta x)}{\cosh(bx)} \, dx =
\frac{1}{4b} \Bigl[ \psi\bigl(\tfrac34 + \tfrac{\alpha+\beta}{4b}\bigr) -
\psi\bigl(\tfrac14 + \tfrac{\alpha-\beta}{4b}\bigr) +
\psi\bigl(\tfrac34 + \tfrac{\alpha-\beta}{4b}\bigr) -
\psi\bigl(\tfrac14 + \tfrac{\alpha+\beta}{4b}\bigr) \Bigr].
$$

The source prints only the condition $\operatorname{Re}(\alpha + b - \beta) > 0$; the condition
$\operatorname{Re}(\alpha + b + \beta) > 0$ is also needed, since the integrand is even in $\beta$.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Lemma 1.
-/
public theorem_wanted watson_cosh_integral_digamma
    (b : ℝ) (α β : ℂ) (hb : 0 < b)
    (hminus : 0 < (α + (b : ℂ) - β).re)
    (hplus : 0 < (α + (b : ℂ) + β).re) :
    IntegrableOn
        (fun x : ℝ =>
          Complex.exp (-α * (x : ℂ)) * Complex.cosh (β * (x : ℂ)) /
            Complex.cosh ((b : ℂ) * (x : ℂ)))
        (Set.Ioi 0) ∧
      (∫ (x : ℝ) in Set.Ioi 0,
          Complex.exp (-α * (x : ℂ)) * Complex.cosh (β * (x : ℂ)) /
            Complex.cosh ((b : ℂ) * (x : ℂ))) =
        (1 / (4 * (b : ℂ))) *
          (Complex.digamma ((3 / 4 : ℂ) + (α + β) / (4 * (b : ℂ))) -
            Complex.digamma ((1 / 4 : ℂ) + (α - β) / (4 * (b : ℂ))) +
            Complex.digamma ((3 / 4 : ℂ) + (α - β) / (4 * (b : ℂ))) -
            Complex.digamma ((1 / 4 : ℂ) + (α + β) / (4 * (b : ℂ))))

/--
**Watson expansion terms.** For natural numbers $r$, $n$ and $\nu$, let $B_{2r}$ be the $2r$th
Bernoulli number and let $\mathcal{H}_{2r-1}(\nu/n) = \cot^{(2r-1)}(\pi\nu/n)$ be the
$(2r-1)$st derivative of the cotangent evaluated at $\pi\nu/n$. The $r$th Watson expansion term is
the real number
$$
\Bigl(1 - \frac{1}{2^{2r-1}}\Bigr)
\frac{\pi^{2r-1} B_{2r} \, \mathcal{H}_{2r-1}(\nu/n)}{(2r)! \, n^{2r-1}}.
$$
Here $2r - 1$ is computed in the natural numbers, so for $r = 0$ the factor $1 - 1/2^{2r-1}$ is $0$
and the term vanishes.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Theorem 3 (printed as Theorem 4).
-/
public noncomputable def watsonExpansionTerm (r n ν : ℕ) : ℝ :=
  (1 - 1 / (2 : ℝ) ^ (2 * r - 1)) * Real.pi ^ (2 * r - 1) *
      (((bernoulli (2 * r) : ℚ) : ℝ)) * watsonOddCotangentDeriv r n ν /
    ((Nat.factorial (2 * r) : ℝ) * (n : ℝ) ^ (2 * r - 1))

/--
**Almost-asymptotic expansion of Watson's cosine sum.** Let $n \ge 2$, $N \ge 2$ and $\nu$ be
natural numbers with $1 \le \nu \le n - 1$, and let
$$
C_n(\nu) = \sum_{l=1}^{n-1} \frac{\cos(2 \pi \nu l / n)}{\sin(\pi l / n)}.
$$
For $r \ge 1$ write
$$
T_r(n, \nu) = \frac{(1 - 2^{1-2r}) \, \pi^{2r-1} B_{2r} \, \cot^{(2r-1)}(\pi \nu / n)}
{(2r)! \, n^{2r-1}},
$$
where $B_{2r}$ is the $2r$-th Bernoulli number and $\cot^{(2r-1)}$ is the $(2r-1)$-st derivative
of the cotangent. Then there is a real number $\lambda$ with $0 < \lambda < 1$ such that
$$
C_n(\nu) = -\frac{2n}{\pi} \log\left(2 \sin\frac{\pi \nu}{n}\right) +
2 \sum_{r=1}^{N-1} T_r(n, \nu) + 2 \lambda \, T_N(n, \nu).
$$

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Theorem 3 (printed as Theorem 4).
-/
public theorem_wanted watson_cos_sum_almost_asymptotic
    (n ν N : ℕ) (hn : 2 ≤ n) (hN : 2 ≤ N) (hνpos : 1 ≤ ν)
    (hνmax : ν ≤ n - 1) :
    ∃ remainder : ℝ, 0 < remainder ∧ remainder < 1 ∧
      watsonCosSum n ν =
        -(2 * (n : ℝ) / Real.pi) *
            Real.log (2 * Real.sin (Real.pi * (ν : ℝ) / (n : ℝ))) +
          2 * (∑ r ∈ Finset.Icc 1 (N - 1), watsonExpansionTerm r n ν) +
          2 * remainder * watsonExpansionTerm N n ν

/--
**The odd cotangent derivatives in Watson's expansion are negative.** Let $r$, $n$ and $\nu$ be
natural numbers with $r \ge 1$ and $1 \le \nu \le n - 1$. Then
$\mathcal{H}_{2r-1}(\nu/n) = \cot^{(2r-1)}(\pi\nu/n)$, the $(2r-1)$st derivative of the cotangent
evaluated at $\pi\nu/n$, is strictly negative.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Theorem 3 (printed as Theorem 4).
-/
public theorem_wanted watson_odd_cotangent_deriv_neg
    (r n ν : ℕ) (hr : 1 ≤ r) (hνpos : 1 ≤ ν) (hνmax : ν ≤ n - 1) :
    watsonOddCotangentDeriv r n ν < 0

/--
**Main part of the asymptotic expansion of Watson's alternating cosecant sum.** For natural numbers
$N$ and $n$, the main part is the real number
$$
M_N(n) = \frac{2 n \log 2}{\pi} + 2 \sum_{r=1}^{N-1}
\frac{(-1)^{r+1} (2^{2r-1} - 1)(2^{2r} - 1) \pi^{2r-1} B_{2r}^2}{r \, (2r)! \, n^{2r-1}},
$$
where $B_{2r}$ is the $2r$-th Bernoulli number. For $N \le 1$ the sum is empty.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 2.
-/
public noncomputable def watsonAlternatingMain (N n : ℕ) : ℝ :=
  2 * (n : ℝ) * Real.log 2 / Real.pi +
    2 * (∑ r ∈ Finset.Icc 1 (N - 1),
      (-1 : ℝ) ^ (r + 1) * ((2 : ℝ) ^ (2 * r - 1) - 1) *
          ((2 : ℝ) ^ (2 * r) - 1) * Real.pi ^ (2 * r - 1) *
          (((bernoulli (2 * r) : ℚ) : ℝ) ^ 2) /
        ((r : ℝ) * (Nat.factorial (2 * r) : ℝ) * (n : ℝ) ^ (2 * r - 1)))

/--
**Complete asymptotic expansion of Watson's alternating cosecant sum.** For natural numbers $N$
and $n$ let $C_n = \sum_{l=1}^{n-1} (-1)^{l+1} / \sin(\pi l / n)$ and
$$
M_N(n) = \frac{2 n \log 2}{\pi} + 2 \sum_{r=1}^{N-1}
\frac{(-1)^{r+1} (2^{2r-1} - 1)(2^{2r} - 1) \pi^{2r-1} B_{2r}^2}{r \, (2r)! \, n^{2r-1}},
$$
where $B_{2r}$ is the $2r$-th Bernoulli number. For every $N \ge 2$ there is a real constant
$K \ge 0$ such that for every even $n \ge 2$,
$$
|C_n - M_N(n)| \le \frac{K}{n^{2N-1}}.
$$
In other words, $C_n = M_N(n) + O(n^{1-2N})$ as $n \to \infty$ through even values.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 2.
-/
public theorem_wanted watson_alternating_complete_asymptotic (N : ℕ) (hN : 2 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, Even n → 2 ≤ n →
      |watsonAlternatingCosecantSum n - watsonAlternatingMain N n| ≤
        K / (n : ℝ) ^ (2 * N - 1)

/--
**Watson's alternating cosecant sum vanishes for odd $n$.** For every odd natural number $n$,
$$
\sum_{l=1}^{n-1} \frac{(-1)^{l+1}}{\sin(\pi l / n)} = 0.
$$

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 2 and Theorem 6.
-/
public theorem_wanted watson_alternating_odd_zero (n : ℕ) (hn : Odd n) :
    watsonAlternatingCosecantSum n = 0

/--
**Two-sided bounds for Watson's alternating cosecant sum.** For every even natural number
$n \ge 2$, the alternating cosecant sum $C_n = \sum_{l=1}^{n-1} (-1)^{l+1} / \sin(\pi l / n)$
satisfies the strict inequalities
$$
\frac{2 n \log 2}{\pi} + \frac{\pi}{12 n} - \frac{7 \pi^3}{1440 n^3} < C_n <
\frac{2 n \log 2}{\pi} + \frac{\pi}{12 n}.
$$
The lower bound consists of the first three terms of the asymptotic expansion of $C_n$ and the
upper bound of the first two.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Theorem 6 and Corollary 3.
-/
public theorem_wanted watson_alternating_sharp_bounds
    (n : ℕ) (heven : Even n) (hn : 2 ≤ n) :
    2 * (n : ℝ) * Real.log 2 / Real.pi + Real.pi / (12 * (n : ℝ)) -
          7 * Real.pi ^ 3 / (1440 * (n : ℝ) ^ 3) <
        watsonAlternatingCosecantSum n ∧
      watsonAlternatingCosecantSum n <
        2 * (n : ℝ) * Real.log 2 / Real.pi + Real.pi / (12 * (n : ℝ))

/--
**Decimal bounds for Watson's alternating cosecant sum.** For every even natural number
$n \ge 4$, the alternating cosecant sum $C_n = \sum_{l=1}^{n-1} (-1)^{l+1} / \sin(\pi l / n)$
satisfies the strict inequalities
$$
\frac{2 n \log 2}{\pi} + \frac{0.252}{n} < C_n < \frac{2 n \log 2}{\pi} + \frac{0.262}{n}.
$$

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 3.
-/
public theorem_wanted watson_alternating_simple_bounds
    (n : ℕ) (heven : Even n) (hn : 4 ≤ n) :
    2 * (n : ℝ) * Real.log 2 / Real.pi + (0.252 : ℝ) / (n : ℝ) <
        watsonAlternatingCosecantSum n ∧
      watsonAlternatingCosecantSum n <
        2 * (n : ℝ) * Real.log 2 / Real.pi + (0.262 : ℝ) / (n : ℝ)

/--
**Vanishing limits of Watson's cosine sum at one sixth and five sixths.** For natural numbers
$n$ and $\nu$ let $C_n(\nu) = \sum_{l=1}^{n-1} \cos(2 \pi \nu l / n) / \sin(\pi l / n)$. As
$m \to \infty$ through the natural numbers, $C_{6m}(m) \to 0$ and $C_{6m}(5m) \to 0$.

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 4.
-/
public theorem_wanted watson_cos_sum_sixth_limits :
    Tendsto (fun m : ℕ => watsonCosSum (6 * m) m) atTop (𝓝 0) ∧
      Tendsto (fun m : ℕ => watsonCosSum (6 * m) (5 * m)) atTop (𝓝 0)

end

end MetaMathlibExt
