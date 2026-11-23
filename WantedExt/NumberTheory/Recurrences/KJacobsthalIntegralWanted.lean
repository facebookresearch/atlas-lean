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
public import MathlibExt.NumberTheory.LucasSequence

namespace MetaMathlibExt

@[expose] public section


/-- **Lucas parameters of the k-Jacobsthal numbers.** For a natural number $k$, the Lucas-sequence
parameters $(P, Q) = (k, -2)$. The Lucas sequences $J_{k,n} = U_n(k, -2)$ and
$j_{k,n} = V_n(k, -2)$ with these parameters are the $k$-Jacobsthal numbers ($J_{k,0} = 0$,
$J_{k,1} = 1$) and the $k$-Jacobsthal–Lucas numbers ($j_{k,0} = 2$, $j_{k,1} = k$); both satisfy
$x_{n+2} = k x_{n+1} + 2 x_n$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Section 1, recurrences (1) and (2). -/
def kJacobsthalParams (k : ℕ) : LucasSequenceParams where
  p := k
  q := -2
  q_ne_zero := by decide

/-- **The second k-Jacobsthal number.** For every natural number $k$, the $k$-Jacobsthal number
$J_{k,2} = U_2(k, -2)$ equals $k$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
proof of Theorem 2. -/
theorem lucasU_kJacobsthalParams_two (k : ℕ) : lucasU (kJacobsthalParams k) 2 = k := by
  simp [lucasU, kJacobsthalParams]

/-- **The $k$-Jacobsthal-Lucas number $j_{k,2}$.** For every natural number $k$, the
$k$-Jacobsthal-Lucas numbers $j_{k,n} = V_n(k, -2)$, the Lucas sequence $V$ with parameters
$(P, Q) = (k, -2)$, satisfy $j_{k,2} = k^2 + 4$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
proof of Theorem 2. -/
theorem lucasV_kJacobsthalParams_two (k : ℕ) :
    lucasV (kJacobsthalParams k) 2 = (k : ℤ) ^ 2 + 4 := by
  simp [lucasV, kJacobsthalParams]
  ring

/-- **Companion $k$-Jacobsthal numbers.** For a natural number $k$ and integers $a, b$, the
companion $k$-Jacobsthal numbers $\mathcal{J}_{k,n}(a, b)$, $n \in \mathbb{N}$, are the integers
defined by $\mathcal{J}_{k,0}(a, b) = a$, $\mathcal{J}_{k,1}(a, b) = b$ and
$\mathcal{J}_{k,n+2}(a, b) = k\,\mathcal{J}_{k,n+1}(a, b) + 2\,\mathcal{J}_{k,n}(a, b)$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Section 4. -/
def companionKJacobsthal (k : ℕ) (a b : ℤ) : ℕ → ℤ
  | 0 => a
  | 1 => b
  | n + 2 => k * companionKJacobsthal k a b (n + 1) + 2 * companionKJacobsthal k a b n

/-- **Recurrence of the companion $k$-Jacobsthal numbers.** For every natural number $k$, all
integers $a, b$ and every natural number $n$, the companion $k$-Jacobsthal numbers satisfy
$\mathcal{J}_{k,n+2}(a, b) = k\,\mathcal{J}_{k,n+1}(a, b) + 2\,\mathcal{J}_{k,n}(a, b)$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Section 4. -/
theorem companionKJacobsthal_add_two (k : ℕ) (a b : ℤ) (n : ℕ) :
    companionKJacobsthal k a b (n + 2) =
      k * companionKJacobsthal k a b (n + 1) + 2 * companionKJacobsthal k a b n :=
  rfl

/-- **The second companion $k$-Jacobsthal number.** For every natural number $k$ and all integers
$a, b$, the companion $k$-Jacobsthal numbers satisfy $\mathcal{J}_{k,2}(a, b) = bk + 2a$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Section 4, list of the first companion numbers. -/
theorem companionKJacobsthal_two (k : ℕ) (a b : ℤ) :
    companionKJacobsthal k a b 2 = b * k + 2 * a := by
  simp [companionKJacobsthal]
  ring

/-- **The $k$-Jacobsthal numbers as companion numbers.** For a natural number $k$, let
$\mathcal{J}_{k,n}(a, b)$ denote the companion $k$-Jacobsthal numbers and $J_{k,n} = U_n(k, -2)$
the $k$-Jacobsthal numbers, the Lucas sequence with parameters $(k, -2)$. Then for every natural
number $n$, $\mathcal{J}_{k,n}(0, 1) = J_{k,n}$: the companion numbers with initial values $0$ and
$1$ are the $k$-Jacobsthal numbers.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Section 4, special cases of the companion numbers. -/
theorem companionKJacobsthal_zero_one (k n : ℕ) :
    companionKJacobsthal k 0 1 n = lucasU (kJacobsthalParams k) n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
      rw [companionKJacobsthal_add_two, ih1, ih2, lucasU_add_two]
      simp [kJacobsthalParams]

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

/-- **Integral representation of Jacobsthal numbers with an offset.** Let $\ell$, $n$ and $r$ be
natural numbers and let $J_n = U_n(1, -2)$ and $j_n = V_n(1, -2)$ be the Jacobsthal and
Jacobsthal–Lucas numbers (the case $k = 1$). Then
$$J_{\ell n + r} = \frac{1}{2^{n+1}} \int_{-1}^{1}
(n J_\ell j_r + J_r j_\ell + 3(n+1) J_\ell J_r x) (j_\ell + 3 J_\ell x)^{n-1} \, dx.$$
Here $n - 1$ is an integer exponent, so for $n = 0$ the power is a reciprocal.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Corollary 4 (`integers-2025-A74-cor-4`). -/
public theorem_wanted jacobsthal_mul_add_eq_integral (ℓ n r : ℕ) :
    (lucasU (kJacobsthalParams 1) (ℓ * n + r) : ℝ) =
      1 / 2 ^ (n + 1) * ∫ x in (-1 : ℝ)..1,
        (n * J[1, ℓ] * jL[1, r] + J[1, r] * jL[1, ℓ] +
            3 * (n + 1) * J[1, ℓ] * J[1, r] * x) * (jL[1, ℓ] + 3 * J[1, ℓ] * x) ^ ((n : ℤ) - 1)

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

/-- **Ratio of consecutive $k$-Jacobsthal numbers.** For every positive integer $k$, the
$k$-Jacobsthal numbers $J_{k,n} = U_n(k, -2)$, the Lucas sequence $U$ with parameters
$(P, Q) = (k, -2)$, satisfy $J_{k,n+1}/J_{k,n} \to (k + \sqrt{k^2 + 8})/2$ as $n \to \infty$,
the quotients taken in $\mathbb{R}$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 8 (`integers-2025-A74-thm-8`). -/
public theorem_wanted tendsto_lucasU_kJacobsthal_ratio (k : ℕ) (hk : 0 < k) :
    Filter.Tendsto
      (fun n : ℕ => (lucasU (kJacobsthalParams k) (n + 1) : ℝ) / lucasU (kJacobsthalParams k) n)
      Filter.atTop (nhds ((k + Δ[k]) / 2))

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

/-- **Generating function of the companion $k$-Jacobsthal numbers.** For every natural number $k$
and all integers $a, b$, the companion $k$-Jacobsthal numbers $\mathcal{J}_{k,n} =
\mathcal{J}_{k,n}(a, b)$ satisfy, in the ring $\mathbb{Z}[[x]]$ of formal power series,
$$\Bigl(\sum_{n \ge 0} \mathcal{J}_{k,n} x^n\Bigr)(1 - kx - 2x^2) = a + (b - ak)x.$$

This is the identity $\sum_{n \ge 0} \mathcal{J}_{k,n} x^n = \frac{a + (b - ak)x}{1 - kx - 2x^2}$
with the denominator cleared.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 10 (`integers-2025-A74-thm-10`). -/
public theorem_wanted companionKJacobsthal_generatingFunction (k : ℕ) (a b : ℤ) :
    PowerSeries.mk (companionKJacobsthal k a b) *
        (1 - PowerSeries.C (k : ℤ) * PowerSeries.X - PowerSeries.C 2 * PowerSeries.X ^ 2) =
      PowerSeries.C a + PowerSeries.C (b - a * k) * PowerSeries.X

/-- **Catalan's identity for the companion $k$-Jacobsthal numbers.** Let $k$ be a natural number,
$a, b$ integers, $\mathcal{J}_{k,m} = \mathcal{J}_{k,m}(a, b)$ the companion $k$-Jacobsthal numbers
and $J_{k,m} = U_m(k, -2)$ the $k$-Jacobsthal numbers. For all natural numbers $r \le n$,
$$
\mathcal{J}_{k,n-r}\,\mathcal{J}_{k,n+r} - \mathcal{J}_{k,n}^2 =
\bigl(a^2 (k^2 + 8) - (2b - ak)^2\bigr)\,(-2)^{n-r-2}\,J_{k,r}^2
$$
in $\mathbb{Q}$, where $(-2)^{n-r-2}$ is an integer power.

With $\Delta_k = \sqrt{k^2 + 8}$, the first factor on the right equals
$(2b - ak + a\Delta_k)(ak - 2b + a\Delta_k)$, the form in which the source states it.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 11 (`integers-2025-A74-thm-11`). -/
public theorem_wanted companionKJacobsthal_catalan (k : ℕ) (a b : ℤ) (n r : ℕ) (hrn : r ≤ n) :
    ((companionKJacobsthal k a b (n - r) * companionKJacobsthal k a b (n + r) -
        companionKJacobsthal k a b n ^ 2 : ℤ) : ℚ) =
      ((a ^ 2 * ((k : ℤ) ^ 2 + 8) - (2 * b - a * k) ^ 2 : ℤ) : ℚ) *
        (-2 : ℚ) ^ ((n : ℤ) - r - 2) * (lucasU (kJacobsthalParams k) r : ℚ) ^ 2

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
