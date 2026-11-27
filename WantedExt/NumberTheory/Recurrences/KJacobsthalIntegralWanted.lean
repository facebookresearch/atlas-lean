/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Integral representations of k-Jacobsthal and k-Jacobsthal-Lucas numbers

Statements from Weerayuth Nilsrakoo and Achariya Nilsrakoo, "An Integral Representation of
k-Jacobsthal and k-Jacobsthal-Lucas Numbers", *INTEGERS* 25 (2025), Article A74
(<https://math.colgate.edu/~integers/z74/z74.pdf>).

The `k`-Jacobsthal numbers `J_{k,n}` (`0, 1`, `J_{k,n} = k J_{k,n-1} + 2 J_{k,n-2}`) and the
`k`-Jacobsthal-Lucas numbers `j_{k,n}` (`2, k`, same recurrence) are the Lucas sequences
`lucasU` and `lucasV` with parameters `(P, Q) = (k, -2)` (`kJacobsthalParams k`).
`Δ_k = √(k² + 8)` and `σ_k = (k + Δ_k)/2`. The companion numbers `𝒥_{k,n}(a, b)` (`a, b`,
same recurrence) are `companionKJacobsthal k a b`. Integrals are interval integrals over
`[-1, 1]`; the exponent `n - 1` is an integer power. At `n = 0` the integrands without a
prefactor `n` are the paper's `(…)(…)^{-1}`, a.e. constant. The statements with a prefactor
`n` (Theorem 1, Theorem 2 (i), Corollary 1, Corollary 2 (i)) hold at `n = 0` only because that
prefactor is `0`: their integrand is `(…)^{-1}`, which in Theorem 1 and Corollary 1 can have a
pole in `[-1, 1]` (`k = ℓ = 1` gives `(1 + 3x)^{-1}`), where `intervalIntegral` returns `0`.

Corollary 6 is not formalized: as printed it is false (see the source audit table).
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.NumberTheory.Recurrences.JacobsthalOffsetIntegral
public import MathlibExt.NumberTheory.Recurrences.KJacobsthal
public import MathlibExt.NumberTheory.Recurrences.KJacobsthalGeneratingFunction
public import MathlibExt.NumberTheory.Recurrences.KJacobsthalIntegralCompanionKJacobsthalCatalan

namespace MetaMathlibExt

@[expose] public section

/-- `J[k, n]` is the real cast of `J_{k,n} = lucasU (kJacobsthalParams k) n`. -/
local notation "J[" k ", " n "]" => (lucasU (kJacobsthalParams k) n : ℝ)
/-- `jL[k, n]` is the real cast of `j_{k,n} = lucasV (kJacobsthalParams k) n`. -/
local notation "jL[" k ", " n "]" => (lucasV (kJacobsthalParams k) n : ℝ)
/-- `Δ[k] = √(k² + 8)`. -/
local notation "Δ[" k "]" => Real.sqrt ((k : ℝ) ^ 2 + 8)

/-- **Binet-type identities for k-Jacobsthal numbers.** Let $k$ and $n$ be natural numbers, let
$J_{k,n} = U_n(k, -2)$ and $j_{k,n} = V_n(k, -2)$ be the $k$-Jacobsthal and
$k$-Jacobsthal–Lucas numbers, and let $\Delta_k = \sqrt{k^2 + 8}$ and $\sigma_k = (k + \Delta_k)/2$.
Then, in $\mathbb{R}$, $j_{k,n} + \Delta_k J_{k,n} = 2\sigma_k^n$ and
$j_{k,n} - \Delta_k J_{k,n} = 2(-2)^n / \sigma_k^n$, and, in $\mathbb{Z}$,
$j_{k,n}^2 - (k^2 + 8) J_{k,n}^2 = (-2)^{n+2}$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Lemma 1 (`integers-2025-A74-lem-1`). -/
public theorem_wanted kJacobsthal_binet_identities (k n : ℕ) :
    jL[k, n] + Δ[k] * J[k, n] = 2 * ((k + Δ[k]) / 2) ^ n ∧
      jL[k, n] - Δ[k] * J[k, n] = 2 * (-2) ^ n / ((k + Δ[k]) / 2) ^ n ∧
      lucasV (kJacobsthalParams k) n ^ 2 - ((k : ℤ) ^ 2 + 8) * lucasU (kJacobsthalParams k) n ^ 2 =
        (-2) ^ (n + 2)

/-- **Addition formulas for k-Jacobsthal numbers.** Let $k$, $m$ and $n$ be natural numbers and
let $J_{k,n} = U_n(k, -2)$ and $j_{k,n} = V_n(k, -2)$ be the $k$-Jacobsthal and
$k$-Jacobsthal–Lucas numbers. Then $2J_{k,m+n} = J_{k,m} j_{k,n} + J_{k,n} j_{k,m}$ and
$2j_{k,m+n} = j_{k,m} j_{k,n} + (k^2 + 8) J_{k,m} J_{k,n}$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Lemma 2 (`integers-2025-A74-lem-2`). -/
public theorem_wanted kJacobsthal_add_formulas (k m n : ℕ) :
    2 * lucasU (kJacobsthalParams k) (m + n) =
        lucasU (kJacobsthalParams k) m * lucasV (kJacobsthalParams k) n +
          lucasU (kJacobsthalParams k) n * lucasV (kJacobsthalParams k) m ∧
      2 * lucasV (kJacobsthalParams k) (m + n) =
        lucasV (kJacobsthalParams k) m * lucasV (kJacobsthalParams k) n +
          ((k : ℤ) ^ 2 + 8) * lucasU (kJacobsthalParams k) m * lucasU (kJacobsthalParams k) n

/-- **Integral representation of k-Jacobsthal numbers at multiples.** Let $k$, $\ell$ and $n$ be
natural numbers, let $J_{k,n} = U_n(k, -2)$ and $j_{k,n} = V_n(k, -2)$ be the $k$-Jacobsthal and
$k$-Jacobsthal–Lucas numbers, and let $\Delta_k = \sqrt{k^2 + 8}$. Then
$$J_{k,\ell n} = \frac{n J_{k,\ell}}{2^n} \int_{-1}^{1}
(j_{k,\ell} + \Delta_k J_{k,\ell} x)^{n-1} \, dx.$$
Here $n - 1$ is an integer exponent, so for $n = 0$ the power is a reciprocal.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 1 (`integers-2025-A74-thm-1`). -/
public theorem_wanted lucasU_kJacobsthal_mul_eq_integral (k ℓ n : ℕ) :
    (lucasU (kJacobsthalParams k) (ℓ * n) : ℝ) =
      n * J[k, ℓ] / 2 ^ n *
        ∫ x in (-1 : ℝ)..1, (jL[k, ℓ] + Δ[k] * J[k, ℓ] * x) ^ ((n : ℤ) - 1)

/-- **Integral representation of even- and odd-indexed k-Jacobsthal numbers.** Let $k$ and $n$
be natural numbers, let $J_{k,n} = U_n(k, -2)$ be the $k$-Jacobsthal numbers and let
$\Delta_k = \sqrt{k^2 + 8}$. Then
$$J_{k,2n} = \frac{kn}{2^n} \int_{-1}^{1} (k^2 + 4 + k \Delta_k x)^{n-1} \, dx$$
and
$$J_{k,2n+1} = \frac{1}{2^{n+1}} \int_{-1}^{1} (nk^2 + k^2 + 4 + k(n+1) \Delta_k x)
(k^2 + 4 + k \Delta_k x)^{n-1} \, dx.$$
Here $n - 1$ is an integer exponent, so for $n = 0$ the power is a reciprocal.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 2 (`integers-2025-A74-thm-2`). -/
public theorem_wanted lucasU_kJacobsthal_even_odd_eq_integral (k n : ℕ) :
    (lucasU (kJacobsthalParams k) (2 * n) : ℝ) =
        k * n / 2 ^ n * ∫ x in (-1 : ℝ)..1, ((k : ℝ) ^ 2 + 4 + k * Δ[k] * x) ^ ((n : ℤ) - 1) ∧
      (lucasU (kJacobsthalParams k) (2 * n + 1) : ℝ) =
        1 / 2 ^ (n + 1) * ∫ x in (-1 : ℝ)..1,
          (n * (k : ℝ) ^ 2 + k ^ 2 + 4 + k * (n + 1) * Δ[k] * x) *
            ((k : ℝ) ^ 2 + 4 + k * Δ[k] * x) ^ ((n : ℤ) - 1)

/-- **Integral representation of k-Jacobsthal–Lucas numbers at multiples.** Let $k$, $\ell$ and
$n$ be natural numbers, let $J_{k,n} = U_n(k, -2)$ and $j_{k,n} = V_n(k, -2)$ be the
$k$-Jacobsthal and $k$-Jacobsthal–Lucas numbers, and let $\Delta_k = \sqrt{k^2 + 8}$. Then
$$j_{k,\ell n} = \frac{1}{2^n} \int_{-1}^{1} (j_{k,\ell} + (n+1) \Delta_k J_{k,\ell} x)
(j_{k,\ell} + \Delta_k J_{k,\ell} x)^{n-1} \, dx.$$
Here $n - 1$ is an integer exponent, so for $n = 0$ the power is a reciprocal.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 3 (`integers-2025-A74-thm-3`). -/
public theorem_wanted lucasV_kJacobsthal_mul_eq_integral (k ℓ n : ℕ) :
    (lucasV (kJacobsthalParams k) (ℓ * n) : ℝ) =
      1 / 2 ^ n * ∫ x in (-1 : ℝ)..1,
        (jL[k, ℓ] + (n + 1) * Δ[k] * J[k, ℓ] * x) * (jL[k, ℓ] + Δ[k] * J[k, ℓ] * x) ^ ((n : ℤ) - 1)

/-- **Integral representation of even- and odd-indexed k-Jacobsthal–Lucas numbers.** Let $k$ and
$n$ be natural numbers, let $j_{k,n} = V_n(k, -2)$ be the $k$-Jacobsthal–Lucas numbers and let
$\Delta_k = \sqrt{k^2 + 8}$. Then
$$j_{k,2n} = \frac{1}{2^n} \int_{-1}^{1} (k^2 + 4 + k(n+1) \Delta_k x)
(k^2 + 4 + k \Delta_k x)^{n-1} \, dx$$
and
$$j_{k,2n+1} = \frac{k}{2^{n+1}} \int_{-1}^{1} (n(k^2 + 8) + k^2 + 4 + k(n+1) \Delta_k x)
(k^2 + 4 + k \Delta_k x)^{n-1} \, dx.$$
Here $n - 1$ is an integer exponent, so for $n = 0$ the power is a reciprocal.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 6 (`integers-2025-A74-thm-6`). -/
public theorem_wanted lucasV_kJacobsthal_even_odd_eq_integral (k n : ℕ) :
    (lucasV (kJacobsthalParams k) (2 * n) : ℝ) =
        1 / 2 ^ n * ∫ x in (-1 : ℝ)..1,
          ((k : ℝ) ^ 2 + 4 + k * (n + 1) * Δ[k] * x) *
            ((k : ℝ) ^ 2 + 4 + k * Δ[k] * x) ^ ((n : ℤ) - 1) ∧
      (lucasV (kJacobsthalParams k) (2 * n + 1) : ℝ) =
        k / 2 ^ (n + 1) * ∫ x in (-1 : ℝ)..1,
          (n * ((k : ℝ) ^ 2 + 8) + k ^ 2 + 4 + k * (n + 1) * Δ[k] * x) *
            ((k : ℝ) ^ 2 + 4 + k * Δ[k] * x) ^ ((n : ℤ) - 1)

/-- **Integral representation of Jacobsthal numbers at multiples.** Let $\ell$ and $n$ be natural
numbers and let $J_n = U_n(1, -2)$ and $j_n = V_n(1, -2)$ be the Jacobsthal and
Jacobsthal–Lucas numbers (the case $k = 1$). Then
$$J_{\ell n} = \frac{n J_\ell}{2^n} \int_{-1}^{1} (j_\ell + 3 J_\ell x)^{n-1} \, dx.$$
Here $n - 1$ is an integer exponent, so for $n = 0$ the power is a reciprocal.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Corollary 1 (`integers-2025-A74-cor-1`). -/
public theorem_wanted jacobsthal_mul_eq_integral (ℓ n : ℕ) :
    (lucasU (kJacobsthalParams 1) (ℓ * n) : ℝ) =
      n * J[1, ℓ] / 2 ^ n * ∫ x in (-1 : ℝ)..1, (jL[1, ℓ] + 3 * J[1, ℓ] * x) ^ ((n : ℤ) - 1)

/-- **Integral formulas for even- and odd-indexed Jacobsthal numbers.** Let $J_n = U_n(1, -2)$ be
the Jacobsthal numbers ($J_0 = 0$, $J_1 = 1$, $J_{n+2} = J_{n+1} + 2J_n$). For every natural
number $n$, in $\mathbb{R}$,
$$
J_{2n} = \frac{n}{2^n} \int_{-1}^{1} (5 + 3x)^{n-1}\,dx \quad\text{and}\quad
J_{2n+1} = \frac{1}{2^{n+1}} \int_{-1}^{1} \bigl(n + 5 + 3(n+1)x\bigr)(5 + 3x)^{n-1}\,dx,
$$
where $(5 + 3x)^{n-1}$ is an integer power (for $n = 0$ it is $(5 + 3x)^{-1}$).

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Corollary 2 (`integers-2025-A74-cor-2`). -/
public theorem_wanted jacobsthal_even_odd_eq_integral (n : ℕ) :
    (lucasU (kJacobsthalParams 1) (2 * n) : ℝ) =
        n / 2 ^ n * ∫ x in (-1 : ℝ)..1, (5 + 3 * x) ^ ((n : ℤ) - 1) ∧
      (lucasU (kJacobsthalParams 1) (2 * n + 1) : ℝ) =
        1 / 2 ^ (n + 1) * ∫ x in (-1 : ℝ)..1,
          (n + 5 + 3 * (n + 1) * x) * (5 + 3 * x) ^ ((n : ℤ) - 1)

/-- **Integral representation of the Jacobsthal-Lucas numbers at multiples of an index.** Let
$J_m = U_m(1, -2)$ be the Jacobsthal numbers and $j_m = V_m(1, -2)$ the Jacobsthal-Lucas numbers
($j_0 = 2$, $j_1 = 1$, $j_{m+2} = j_{m+1} + 2j_m$). For all natural numbers $\ell$ and $n$, in
$\mathbb{R}$,
$$
j_{\ell n} = \frac{1}{2^n} \int_{-1}^{1}
\bigl(j_\ell + 3(n+1) J_\ell\,x\bigr)(j_\ell + 3J_\ell x)^{n-1}\,dx,
$$
where $(j_\ell + 3J_\ell x)^{n-1}$ is an integer power (for $n = 0$ it is the reciprocal).

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Corollary 3 (`integers-2025-A74-cor-3`). -/
public theorem_wanted jacobsthalLucas_mul_eq_integral (ℓ n : ℕ) :
    (lucasV (kJacobsthalParams 1) (ℓ * n) : ℝ) =
      1 / 2 ^ n * ∫ x in (-1 : ℝ)..1,
        (jL[1, ℓ] + 3 * (n + 1) * J[1, ℓ] * x) * (jL[1, ℓ] + 3 * J[1, ℓ] * x) ^ ((n : ℤ) - 1)

/-- **Integral representation of the Jacobsthal-Lucas numbers along arithmetic progressions.**
Let $J_m = U_m(1, -2)$ be the Jacobsthal numbers and $j_m = V_m(1, -2)$ the Jacobsthal-Lucas
numbers ($j_0 = 2$, $j_1 = 1$, $j_{m+2} = j_{m+1} + 2j_m$). For all natural numbers $\ell$, $n$
and $r$, in $\mathbb{R}$,
$$
j_{\ell n + r} = \frac{1}{2^{n+1}} \int_{-1}^{1}
\bigl(9n J_\ell J_r + j_\ell j_r + 3(n+1) J_\ell j_r\,x\bigr)(j_\ell + 3J_\ell x)^{n-1}\,dx,
$$
where $(j_\ell + 3J_\ell x)^{n-1}$ is an integer power (for $n = 0$ it is the reciprocal).

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Corollary 5 (`integers-2025-A74-cor-5`). -/
public theorem_wanted jacobsthalLucas_mul_add_eq_integral (ℓ n r : ℕ) :
    (lucasV (kJacobsthalParams 1) (ℓ * n + r) : ℝ) =
      1 / 2 ^ (n + 1) * ∫ x in (-1 : ℝ)..1,
        (9 * n * J[1, ℓ] * J[1, r] + jL[1, ℓ] * jL[1, r] +
            3 * (n + 1) * J[1, ℓ] * jL[1, r] * x) * (jL[1, ℓ] + 3 * J[1, ℓ] * x) ^ ((n : ℤ) - 1)

/-- **Companion $k$-Jacobsthal numbers via Lucas sequences.** For a natural number $k$ and
integers $a, b$, let $\mathcal{J}_{k,n}(a, b)$ be the companion $k$-Jacobsthal numbers, and let
$J_{k,n} = U_n(k, -2)$ and $j_{k,n} = V_n(k, -2)$ be the $k$-Jacobsthal and $k$-Jacobsthal–Lucas
numbers, the Lucas sequences $U$ and $V$ with parameters $(P, Q) = (k, -2)$. Then for every
natural number $n$, $2\,\mathcal{J}_{k,n}(a, b) = a\,j_{k,n} + (2b - ak)\,J_{k,n}$.

The source states this as $\mathcal{J}_{k,n} = \tfrac{a}{2} j_{k,n} + \tfrac{2b - ak}{2} J_{k,n}$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 9 (`integers-2025-A74-thm-9`). -/
public theorem_wanted two_mul_companionKJacobsthal (k : ℕ) (a b : ℤ) (n : ℕ) :
    2 * companionKJacobsthal k a b n =
      a * lucasV (kJacobsthalParams k) n + (2 * b - a * k) * lucasU (kJacobsthalParams k) n

/-- **Integral representation of the companion $k$-Jacobsthal numbers.** Let $k$, $\ell$, $n$ be
natural numbers and $a, b$ integers. Write $\mathcal{J}_{k,m} = \mathcal{J}_{k,m}(a, b)$ for the
companion $k$-Jacobsthal numbers, $J_{k,m} = U_m(k, -2)$ and $j_{k,m} = V_m(k, -2)$ for the
$k$-Jacobsthal and $k$-Jacobsthal-Lucas numbers, and $\Delta_k = \sqrt{k^2 + 8}$. Then, in
$\mathbb{R}$,
$$
\mathcal{J}_{k,\ell n} = \frac{1}{2^{n+1}} \int_{-1}^{1}
\bigl(a\,j_{k,\ell} + (2b - ak)\,n\,J_{k,\ell} + a(n+1)\Delta_k J_{k,\ell}\,x\bigr)
\bigl(j_{k,\ell} + \Delta_k J_{k,\ell}\,x\bigr)^{n-1}\,dx,
$$
where the power $n - 1$ is an integer power (for $n = 0$ it is the reciprocal).

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 12 (`integers-2025-A74-thm-12`). -/
public theorem_wanted companionKJacobsthal_mul_eq_integral (k ℓ n : ℕ) (a b : ℤ) :
    (companionKJacobsthal k a b (ℓ * n) : ℝ) =
      1 / 2 ^ (n + 1) * ∫ x in (-1 : ℝ)..1,
        (a * jL[k, ℓ] + (2 * b - a * k) * n * J[k, ℓ] +
            a * (n + 1) * Δ[k] * J[k, ℓ] * x) * (jL[k, ℓ] + Δ[k] * J[k, ℓ] * x) ^ ((n : ℤ) - 1)

end

end MetaMathlibExt
