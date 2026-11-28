/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import MathlibExt.Analysis.SpecialFunctions.Trigonometric.ArcsinQuotientDerivatives
public import MathlibExt.Analysis.SpecialFunctions.Trigonometric.CotangentLimit
public import MathlibExt.Analysis.SpecialFunctions.Trigonometric.HalfPeriodSineSumEven
public import MathlibExt.Analysis.SpecialFunctions.Trigonometric.CosineAlternatingIntegralLimit
public import MathlibExt.Analysis.SpecialFunctions.Trigonometric.CosinePowerAreaRecurrence
public import MathlibExt.Analysis.SpecialFunctions.Trigonometric.CosinePowerAreaDoubleFactorial

namespace MetaMathlibExt

@[expose] public section

open Real Filter Topology

/-- **The area between cosine powers vanishes for exponent zero.** For natural numbers $n$ and
$k$, let $A_n(k) = \int_0^\pi |\cos^n x - \cos^n(kx)|\,dx$ be the area between $\cos^n x$ and
$\cos^n(kx)$ on $[0, \pi]$. Then $A_0(k) = 0$ for every natural number $k$, since both curves are
then the constant $1$.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Eq. (1). -/
public theorem cosPowArea_zero_left (k : ℕ) : cosPowArea 0 k = 0 := by
  simp [cosPowArea]

/-- **The area between cosine powers vanishes at frequency one.** For natural numbers $n$ and $k$,
let $A_n(k) = \int_0^\pi |\cos^n x - \cos^n(kx)|\,dx$ be the area between $\cos^n x$ and
$\cos^n(kx)$ on $[0, \pi]$. Then $A_n(1) = 0$ for every natural number $n$, since the two curves
then coincide.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Eq. (1). -/
public theorem cosPowArea_one_right (n : ℕ) : cosPowArea n 1 = 0 := by
  simp [cosPowArea]

/-- **Area between $\cos^n x$ and $\cos^n(kx)$ in the limit, odd $n$.** Let $n$ be an odd natural
number. As $k \to \infty$ through the natural numbers, the area
$\int_0^\pi |\cos^n x - \cos^n(kx)|\,dx$ between $\cos^n x$ and $\cos^n(kx)$ on $[0, \pi]$
converges to
$$\frac{8}{2^{n-1}\pi} \sum_{j=0}^{(n-1)/2} \frac{\binom{n}{j}}{(n-2j)^2}.$$

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 1
(`jis-2025-25.2.3-thm-1`). -/
public theorem_wanted tendsto_cosPowArea_of_odd {n : ℕ} (hn : Odd n) :
    Tendsto (fun k => cosPowArea n k) atTop
      (𝓝 (8 / (2 ^ (n - 1) * π) *
        ∑ j ∈ Finset.range ((n - 1) / 2 + 1), (n.choose j : ℝ) / ((n : ℝ) - 2 * j) ^ 2))

/-- **Limiting area between even cosine powers.** For natural numbers $n$ and $k$, let
$A_n(k) = \int_0^\pi |\cos^n x - \cos^n(kx)|\,dx$. As $k \to \infty$ through the natural numbers:
if $n \equiv 2 \pmod 4$, then
$$A_n(k) \to \frac{16}{2^n \pi} \sum_{j=0}^{(n-2)/4} \frac{\binom{n}{2j}}{(n/2 - 2j)^2},$$
and if $n \equiv 0 \pmod 4$, then
$$A_n(k) \to \frac{16}{2^n \pi} \sum_{j=0}^{(n-4)/4} \frac{\binom{n}{2j+1}}{(n/2 - 2j - 1)^2}.$$
For $n = 0$ the right-hand side is $0$, as is $A_0(k)$ for every $k$, so no positivity hypothesis
is needed.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 2
(`jis-2025-25.2.3-thm-2`). -/
public theorem_wanted tendsto_cosPowArea_of_even (n : ℕ) :
    (n % 4 = 2 → Tendsto (fun k => cosPowArea n k) atTop
      (𝓝 (16 / (2 ^ n * π) * ∑ j ∈ Finset.range ((n - 2) / 4 + 1),
        (n.choose (2 * j) : ℝ) / ((n : ℝ) / 2 - 2 * j) ^ 2))) ∧
    (n % 4 = 0 → Tendsto (fun k => cosPowArea n k) atTop
      (𝓝 (16 / (2 ^ n * π) * ∑ j ∈ Finset.range ((n - 4) / 4 + 1),
        (n.choose (2 * j + 1) : ℝ) / ((n : ℝ) / 2 - (2 * j + 1)) ^ 2)))

/-- **Alternating integral sums of $\cos qx - \cos qkx$ for even $q$ and odd $k$.** Let $q$ be an
even natural number, for each natural number $m$ put $k = 2m + 1$, and let
$f(x) = \cos(qx) - \cos(qkx)$. Then, as $m \to \infty$,
$$\sum_{\ell=1}^{m} \left(\int_{(\ell-1)\pi/(k-1)}^{\ell\pi/(k+1)} f(x)\,dx -
\int_{\ell\pi/(k+1)}^{\ell\pi/(k-1)} f(x)\,dx\right)$$
tends to $0$ if $q \equiv 0 \pmod 4$ and to $16/(q^2\pi)$ if $q \equiv 2 \pmod 4$.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 10
(`jis-2025-25.2.3-lem-10`). -/
public theorem_wanted tendsto_sum_integral_cos_sub_cos_odd_even {q : ℕ} (hq : Even q) :
    Tendsto (fun m : ℕ => ∑ l ∈ Finset.Icc 1 m,
      ((∫ x in (((l : ℝ) - 1) * π / ((2 * m + 1 : ℝ) - 1))..((l : ℝ) * π / ((2 * m + 1 : ℝ) + 1)),
          (cos (q * x) - cos (q * (2 * m + 1 : ℝ) * x))) -
        ∫ x in ((l : ℝ) * π / ((2 * m + 1 : ℝ) + 1))..((l : ℝ) * π / ((2 * m + 1 : ℝ) - 1)),
          (cos (q * x) - cos (q * (2 * m + 1 : ℝ) * x)))) atTop
      (𝓝 (if q % 4 = 0 then 0 else 16 / ((q : ℝ) ^ 2 * π)))

end

end MetaMathlibExt
