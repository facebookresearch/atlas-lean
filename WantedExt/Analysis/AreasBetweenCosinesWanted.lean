/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

namespace MetaMathlibExt

@[expose] public section

open Real Filter Topology

/-- **Area between powers of cosines.** For natural numbers $n$ and $k$, the area between the
curves $y = \cos^n x$ and $y = \cos^n(kx)$ on $[0, \pi]$ is
$A_n(k) = \int_0^\pi |\cos^n x - \cos^n(kx)|\,dx$, where $\cos^n x$ means $(\cos x)^n$.

The paper's $A_n$ is the limit of $A_n(k)$ as $k \to \infty$ (Eq. (1)), with $k$ running over
the natural numbers.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Eq. (1). -/
public noncomputable def cosPowArea (n k : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..π, |cos x ^ n - cos (k * x) ^ n|

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

/-- **Recursion for the limiting areas between cosine powers.** For natural numbers $n$ and $k$,
let $A_n(k) = \int_0^\pi |\cos^n x - \cos^n(kx)|\,dx$. For every natural number $n \ge 3$ there
are real numbers $L$ and $L'$ such that $A_n(k) \to L$ and $A_{n-2}(k) \to L'$ as $k \to \infty$
through the natural numbers, and $L = \frac{n-1}{n} L' + \frac{c}{n^2 \pi}$, where $c = 8$ if $n$
is odd and $c = 16$ if $n$ is even.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 3
(`jis-2025-25.2.3-thm-3`). -/
public theorem_wanted cosPowArea_limit_recursion {n : ℕ} (hn : 3 ≤ n) :
    ∃ L L' : ℝ, Tendsto (fun k => cosPowArea n k) atTop (𝓝 L) ∧
      Tendsto (fun k => cosPowArea (n - 2) k) atTop (𝓝 L') ∧
      L = ((n : ℝ) - 1) / n * L' + (if Odd n then 8 else 16) / ((n : ℝ) ^ 2 * π)

/-- **Limiting area between cosine powers via double factorials.** For natural numbers $n$ and
$k$, let $A_n(k) = \int_0^\pi |\cos^n x - \cos^n(kx)|\,dx$. As $k \to \infty$ through the natural
numbers: if $n$ is odd, then
$$A_n(k) \to \frac{8 \, n!}{\pi (n!!)^2} \sum_{j=0}^{(n-1)/2} \frac{(2j-1)!!}{(2j)!! (2j+1)},$$
and if $n \ge 2$ is even, then
$$A_n(k) \to \frac{16 \, n!}{\pi (n!!)^2} \sum_{j=0}^{(n-2)/2} \frac{(2j)!!}{(2j+1)!! (2j+2)}.$$
Here $(-1)!! = 1$ and $0!! = 1$.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 4
(`jis-2025-25.2.3-thm-4`). -/
public theorem_wanted tendsto_cosPowArea_doubleFactorial (n : ℕ) :
    (Odd n → Tendsto (fun k => cosPowArea n k) atTop
      (𝓝 (8 / π * ((n.factorial : ℝ) / (n.doubleFactorial : ℝ) ^ 2) *
        ∑ j ∈ Finset.range ((n - 1) / 2 + 1),
          ((2 * j - 1).doubleFactorial : ℝ) /
            ((2 * j).doubleFactorial * (2 * j + 1))))) ∧
    (Even n → 0 < n → Tendsto (fun k => cosPowArea n k) atTop
      (𝓝 (16 / π * ((n.factorial : ℝ) / (n.doubleFactorial : ℝ) ^ 2) *
        ∑ j ∈ Finset.range ((n - 2) / 2 + 1),
          ((2 * j).doubleFactorial : ℝ) /
            ((2 * j + 1).doubleFactorial * (2 * j + 2)))))

/-- **Double-factorial sums as derivatives of arcsine quotients.** Let $n$ be a natural number.
If $n$ is odd, the $n$th derivative at $0$ of $x \mapsto \arcsin x / (1 - x)$ is
$$n! \sum_{j=0}^{(n-1)/2} \frac{(2j-1)!!}{(2j)!!\,(2j+1)},$$
and if $n \ge 2$ is even, the $n$th derivative at $0$ of $x \mapsto (\arcsin x)^2 / (2(1 - x))$ is
$$n! \sum_{j=0}^{(n-2)/2} \frac{(2j)!!}{(2j+1)!!\,(2j+2)},$$
where $(-1)!! = 1$ and $0!! = 1$.

These are the $n$th terms of the exponential generating functions of $\arcsin x / (1 - x)$
(OEIS A296726) and of $(\arcsin x)^2 / (2(1 - x))$ (OEIS A372324).

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 4
(`jis-2025-25.2.3-thm-4`). -/
public theorem_wanted iteratedDeriv_arcsin_div_one_sub_doubleFactorial (n : ℕ) :
    (Odd n → iteratedDeriv n (fun x => arcsin x / (1 - x)) 0 =
      n.factorial * ∑ j ∈ Finset.range ((n - 1) / 2 + 1),
        ((2 * j - 1).doubleFactorial : ℝ) / ((2 * j).doubleFactorial * (2 * j + 1))) ∧
    (Even n → 0 < n → iteratedDeriv n (fun x => arcsin x ^ 2 / (2 * (1 - x))) 0 =
      n.factorial * ∑ j ∈ Finset.range ((n - 2) / 2 + 1),
        ((2 * j).doubleFactorial : ℝ) / ((2 * j + 1).doubleFactorial * (2 * j + 2)))

/-- **Half-period sine sum for even modulus.** Let $N$ be a positive even natural number. For
every natural number $q$, $\sum_{\ell=1}^{N/2} \sin(2\pi q \ell / N)$ equals $0$ if $q$ is even
and $\cot(q\pi / N)$ if $q$ is odd.

The paper also assumes $q > 0$; for $q = 0$ both sides are $0$.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 5
(`jis-2025-25.2.3-lem-5`). -/
public theorem_wanted sum_sin_two_pi_mul_div_of_even {N : ℕ} (hN : 0 < N) (hNe : Even N)
    (q : ℕ) :
    ∑ l ∈ Finset.Icc 1 (N / 2), sin (q * l * 2 * π / N) =
      if Even q then 0 else cot (q * π / N)

/-- **Half-period sine sum for odd modulus.** Let $N$ be an odd natural number. For every
natural number $q$, $\sum_{\ell=1}^{(N-1)/2} \sin(2\pi q \ell / N)$ equals
$-\frac{1}{2} \tan\frac{q\pi}{2N}$ if $q$ is even and $\frac{1}{2} \cot\frac{q\pi}{2N}$ if $q$ is
odd.

The paper also assumes $q > 0$; for $q = 0$ both sides are $0$.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 6
(`jis-2025-25.2.3-lem-6`). -/
public theorem_wanted sum_sin_two_pi_mul_div_of_odd {N : ℕ} (hN : Odd N) (q : ℕ) :
    ∑ l ∈ Finset.Icc 1 ((N - 1) / 2), sin (q * l * 2 * π / N) =
      if Even q then -(1 / 2) * tan (q * π / (2 * N)) else 1 / 2 * cot (q * π / (2 * N))

/-- **Half-step sine sum for even modulus and even multiplier.** Let $N$ be a positive even
natural number and $q$ an even natural number. Then $\sum_{\ell=1}^{N/2} \sin(q \ell \pi / N)$
equals $0$ if $q \equiv 0 \pmod 4$ and $\cot(q\pi / (2N))$ if $q \equiv 2 \pmod 4$.

The paper also assumes $q > 0$; that hypothesis is dropped here.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 7
(`jis-2025-25.2.3-lem-7`). -/
public theorem_wanted sum_sin_pi_mul_div_of_even_of_even {N q : ℕ} (hN : 0 < N)
    (hNe : Even N) (hq : Even q) :
    ∑ l ∈ Finset.Icc 1 (N / 2), sin (q * l * π / N) =
      if q % 4 = 0 then 0 else cot (q * π / (2 * N))

/-- **The cotangent limit $4/x$.** For every nonzero real number $x$, as $k \to \infty$ through the
natural numbers,
$$\left(\frac{1}{k} - 1\right)\cot\frac{x}{k-1} + \left(\frac{1}{k} + 1\right)\cot\frac{x}{k+1}
\to \frac{4}{x}.$$

The paper states this for every real number $x$; the hypothesis $x \neq 0$ is added because at
$x = 0$ the cotangents and $4/x$ are undefined.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 8
(`jis-2025-25.2.3-lem-8`). -/
public theorem_wanted tendsto_cot_div_pred_add_cot_div_succ {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun k : ℕ => (1 / (k : ℝ) - 1) * cot (x / (k - 1)) +
      (1 / (k : ℝ) + 1) * cot (x / (k + 1))) atTop (𝓝 (4 / x))

/-- **Integral sums of $\cos qkx - \cos qx$ for odd $q$ and odd $k$.** Let $q$ be an odd natural
number, and for each natural number $m$ put $k = 2m + 1$. Then, as $m \to \infty$,
$$\sum_{\ell=1}^{m} \int_{2\pi\ell/(k+1)}^{2\pi\ell/(k-1)} \bigl(\cos(qkx) - \cos(qx)\bigr)\,dx
\to \frac{4}{q^2\pi}.$$

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 9
(`jis-2025-25.2.3-lem-9`). -/
public theorem_wanted tendsto_sum_integral_cos_sub_cos_odd_odd {q : ℕ} (hq : Odd q) :
    Tendsto (fun m : ℕ => ∑ l ∈ Finset.Icc 1 m,
      ∫ x in (2 * π * l / ((2 * m + 1 : ℝ) + 1))..(2 * π * l / ((2 * m + 1 : ℝ) - 1)),
        (cos (q * (2 * m + 1 : ℝ) * x) - cos (q * x))) atTop
      (𝓝 (4 / ((q : ℝ) ^ 2 * π)))

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

/-- **Alternating integral sums of $\cos qx - \cos qkx$ for odd $q$ and even $k$.** Let $q$ be an
odd natural number, for each natural number $m$ put $k = 2m$, and let
$f(x) = \cos(qx) - \cos(qkx)$. Then, as $m \to \infty$,
$$\sum_{\ell=1}^{m} \left(\int_{2(\ell-1)\pi/(k-1)}^{2\ell\pi/(k+1)} f(x)\,dx -
\int_{2\ell\pi/(k+1)}^{2\ell\pi/(k-1)} f(x)\,dx\right) \to \frac{8}{q^2\pi}.$$

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 11
(`jis-2025-25.2.3-lem-11`). -/
public theorem_wanted tendsto_sum_integral_cos_sub_cos_even_odd {q : ℕ} (hq : Odd q) :
    Tendsto (fun m : ℕ => ∑ l ∈ Finset.Icc 1 m,
      ((∫ x in (((l : ℝ) - 1) * 2 * π / ((2 * m : ℝ) - 1))..((l : ℝ) * 2 * π / ((2 * m : ℝ) + 1)),
          (cos (q * x) - cos (q * (2 * m : ℝ) * x))) -
        ∫ x in ((l : ℝ) * 2 * π / ((2 * m : ℝ) + 1))..((l : ℝ) * 2 * π / ((2 * m : ℝ) - 1)),
          (cos (q * x) - cos (q * (2 * m : ℝ) * x)))) atTop
      (𝓝 (8 / ((q : ℝ) ^ 2 * π)))

/-- **Alternating integral sums of $\cos qx - \cos qkx$ for even $q$ and even $k$.** Let $q$ be an
even natural number, for each natural number $m$ put $k = 2m$, and let
$f(x) = \cos(qx) - \cos(qkx)$. Then, as $m \to \infty$,
$$\sum_{\ell=1}^{m} \left(\int_{(\ell-1)\pi/(k-1)}^{\ell\pi/(k+1)} f(x)\,dx -
\int_{\ell\pi/(k+1)}^{\ell\pi/(k-1)} f(x)\,dx\right)$$
tends to $0$ if $q \equiv 0 \pmod 4$ and to $16/(q^2\pi)$ if $q \equiv 2 \pmod 4$.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 12
(`jis-2025-25.2.3-lem-12`). -/
public theorem_wanted tendsto_sum_integral_cos_sub_cos_even_even {q : ℕ} (hq : Even q) :
    Tendsto (fun m : ℕ => ∑ l ∈ Finset.Icc 1 m,
      ((∫ x in (((l : ℝ) - 1) * π / ((2 * m : ℝ) - 1))..((l : ℝ) * π / ((2 * m : ℝ) + 1)),
          (cos (q * x) - cos (q * (2 * m : ℝ) * x))) -
        ∫ x in ((l : ℝ) * π / ((2 * m : ℝ) + 1))..((l : ℝ) * π / ((2 * m : ℝ) - 1)),
          (cos (q * x) - cos (q * (2 * m : ℝ) * x)))) atTop
      (𝓝 (if q % 4 = 0 then 0 else 16 / ((q : ℝ) ^ 2 * π)))

end

end MetaMathlibExt
