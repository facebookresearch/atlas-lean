/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Instances.Rat

/-!
# Explicit Ramanujan-type congruences between Eisenstein series and cusp forms (Lu)

Statements from Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of
Integer Sequences 29 (2026), Article 26.5.1.

All modular forms are handled through their `q`-expansion coefficients, following Section 2 of
the paper: `σ_{w-1}(n)` is the divisor sum for `n ≥ 1`, `σ_{w-1}(0) = -B_w/(2w)` for even
`w ≥ 4`, and weight `0` gives `σ_{-1}(n) = [n = 0]`, so `G_w = ∑_n σ_{w-1}(n) q^n` and
`E_w = G_w / σ_{w-1}(0)`. `Δ = q ∏_{n ≥ 1} (1 - q^n)^{24}` (in `ℚ⟦X⟧`, `∏'` in the
coefficientwise topology), so `τ^{*i} * σ_{w-1}` (additive convolution) is the coefficient
sequence of `Δ^i G_w`. `N_w` is the numerator of `|σ_{w-1}(0)|` (`N_0 = N_2 = 1`), and
`N'_k` is the largest divisor of `N_k` coprime to every `N_{k-12i}`, `1 ≤ i ≤ ⌊k/12⌋`.
A congruence `a ≡ b (mod N)` between rationals means that `(a - b)/N` has denominator coprime
to `N`; a congruence of `q`-series is coefficientwise.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **Lu's congruence for the Eisenstein series $G_k$.** Let $k \ge 12$ be even with $k \ne 14$.
For $w, n \in \mathbb{N}$ let $\sigma_{-1}(n)$ be $1$ if $n = 0$ and $0$ otherwise; for $w \ge 1$
let $\sigma_{w-1}(0) = -B_w/(2w)$, where $B_w$ is the $w$-th Bernoulli number, and
$\sigma_{w-1}(n) = \sum_{d \mid n} d^{w-1}$ for $n \ge 1$. In $\mathbb{Q}[[q]]$ let
$G_w = \sum_{n \ge 0} \sigma_{w-1}(n) q^n$, let $E_w = G_w/\sigma_{w-1}(0)$ for even $w$, and let
$\Delta = q \prod_{j \ge 1} (1 - q^j)^{24}$; for $i, n \in \mathbb{N}$ write $b_i(n)$ for the
coefficient of $q^n$ in $\Delta^i E_{k-12i}$. Let $N_w = 1$ for $w \le 2$, let $N_w$ be the
absolute value of the numerator of $\sigma_{w-1}(0)$ for $w \ge 3$, and let $N'_k$ be the largest
divisor of $N_k$ that is coprime to $N_{k-12i}$ for every $1 \le i \le \lfloor k/12 \rfloor$. For
rationals $x, y$ and a positive integer $N$, $x \equiv y \pmod{N}$ means that $(x - y)/N$ has
denominator coprime to $N$. Let $m = \lfloor k/12 \rfloor - 1$ if
$k \equiv 2 \pmod{12}$ and $m = \lfloor k/12 \rfloor$ otherwise, let $C$ be the $m \times m$ matrix
$(b_i(j))_{1 \le i, j \le m}$, and let
$(\gamma_1, \dots, \gamma_m) = (\sigma_{k-1}(1), \dots, \sigma_{k-1}(m))\, C^{-1}$. Then
$\sigma_{k-1}(n) \equiv \sum_{i=1}^m \gamma_i b_i(n) \pmod{N'_k}$ for every $n \ge 0$, that is,
$G_k \equiv \sum_{i=1}^m \gamma_i \Delta^i E_{k-12i} \pmod{N'_k}$ coefficientwise.

Source: Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of
Integer Sequences 29 (2026), Article 26.5.1, Theorem 1 (`jis-2026-26.5.1-thm-1`). -/
public theorem_wanted eisenstein_congr_sum_delta_pow_mul_eisenstein (k : ℕ) (hk : 12 ≤ k)
    (hke : Even k) (hk14 : k ≠ 14) :
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let m : ℕ := if k % 12 = 2 then k / 12 - 1 else k / 12
    let C : Matrix (Fin m) (Fin m) ℚ := fun i j => b (i.val + 1) (j.val + 1)
    let γ : Fin m → ℚ := Matrix.vecMul (fun j => σ₀ k (j.val + 1)) C⁻¹
    ∀ n : ℕ, ((σ₀ k n - ∑ i : Fin m, γ i * b (i.val + 1) n) / N').den.Coprime N'

/-- **Lu's congruence for the divisor sums $\sigma_{k-1}(n)$.** Let $k \ge 12$ be even with
$k \ne 14$. For $w, n \in \mathbb{N}$ let $\sigma_{-1}(n)$ be $1$ if $n = 0$ and $0$ otherwise;
for $w \ge 1$ let $\sigma_{w-1}(0) = -B_w/(2w)$, where $B_w$ is the $w$-th Bernoulli number, and
$\sigma_{w-1}(n) = \sum_{d \mid n} d^{w-1}$ for $n \ge 1$. In $\mathbb{Q}[[q]]$ let
$G_w = \sum_{n \ge 0} \sigma_{w-1}(n) q^n$ and $\Delta = q \prod_{j \ge 1} (1 - q^j)^{24}$, and
for $i, n \in \mathbb{N}$ let $c_i(n)$ be the coefficient of $q^n$ in $\Delta^i G_{k-12i}$, that
is, the additive convolution $(\tau^{*i} * \sigma_{k-12i-1})(n)$, where $\tau(n)$ is the
coefficient of $q^n$ in $\Delta$. Let $N_w = 1$ for $w \le 2$, let $N_w$ be the absolute value of
the numerator of $\sigma_{w-1}(0)$ for $w \ge 3$, and let $N'_k$ be the largest divisor of $N_k$
that is coprime to $N_{k-12i}$ for every $1 \le i \le \lfloor k/12 \rfloor$. For rationals $x, y$
and a positive integer $N$, $x \equiv y \pmod{N}$ means that $(x - y)/N$ has denominator coprime
to $N$. Let $m = \lfloor k/12 \rfloor - 1$ if $k \equiv 2 \pmod{12}$ and
$m = \lfloor k/12 \rfloor$ otherwise, let $C$ be the $m \times m$ matrix
$\bigl(c_i(j)/\sigma_{k-12i-1}(0)\bigr)_{1 \le i, j \le m}$, and let
$(\gamma_1, \dots, \gamma_m) = (\sigma_{k-1}(1), \dots, \sigma_{k-1}(m))\, C^{-1}$. Then for every
$n \ge 1$, $\sigma_{k-1}(n) \equiv
\sum_{i=1}^m \bigl(\gamma_i/\sigma_{k-12i-1}(0)\bigr)\, c_i(n) \pmod{N'_k}$.

Source: Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of
Integer Sequences 29 (2026), Article 26.5.1, Corollary 3 (`jis-2026-26.5.1-cor-3`). -/
public theorem_wanted sigma_congr_sum_tau_conv_sigma (k : ℕ) (hk : 12 ≤ k) (hke : Even k)
    (hk14 : k ≠ 14) :
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let conv : ℕ → ℕ → ℚ := fun i n => coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i)))
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let m : ℕ := if k % 12 = 2 then k / 12 - 1 else k / 12
    let C : Matrix (Fin m) (Fin m) ℚ := fun i j =>
      conv (i.val + 1) (j.val + 1) / σ₀ (k - 12 * (i.val + 1)) 0
    let γ : Fin m → ℚ := Matrix.vecMul (fun j => σ₀ k (j.val + 1)) C⁻¹
    ∀ n : ℕ, 1 ≤ n → ((σ₀ k n - ∑ i : Fin m,
      γ i / σ₀ (k - 12 * (i.val + 1)) 0 * conv (i.val + 1) n) / N').den.Coprime N'

/-- **Lu's one-term congruence for $G_k$.** Let $k \in \{12, 16, 18, 20, 22, 26\}$.
For $w, n \in \mathbb{N}$ let $\sigma_{-1}(n)$ be $1$ if $n = 0$ and $0$ otherwise; for $w \ge 1$
let $\sigma_{w-1}(0) = -B_w/(2w)$, where $B_w$ is the $w$-th Bernoulli number, and
$\sigma_{w-1}(n) = \sum_{d \mid n} d^{w-1}$ for $n \ge 1$. In $\mathbb{Q}[[q]]$ let
$G_w = \sum_{n \ge 0} \sigma_{w-1}(n) q^n$, let $E_w = G_w/\sigma_{w-1}(0)$ for even $w$, and let
$\Delta = q \prod_{j \ge 1} (1 - q^j)^{24}$; for $i, n \in \mathbb{N}$ write $b_i(n)$ for the
coefficient of $q^n$ in $\Delta^i E_{k-12i}$. Let $N_w = 1$ for $w \le 2$, let $N_w$ be the
absolute value of the numerator of $\sigma_{w-1}(0)$ for $w \ge 3$, and let $N'_k$ be the largest
divisor of $N_k$ that is coprime to $N_{k-12i}$ for every $1 \le i \le \lfloor k/12 \rfloor$. For
rationals $x, y$ and a positive integer $N$, $x \equiv y \pmod{N}$ means that $(x - y)/N$ has
denominator coprime to $N$. Then
$\sigma_{k-1}(n) \equiv b_1(n) \pmod{N'_k}$ for every $n \ge 0$, that is,
$G_k \equiv \Delta E_{k-12} \pmod{N'_k}$ coefficientwise; in particular the congruence holds for
every $n \ge 1$.

Source: Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of
Integer Sequences 29 (2026), Article 26.5.1, Corollary 5 (`jis-2026-26.5.1-cor-5`). -/
public theorem_wanted eisenstein_congr_delta_mul_eisenstein_dim_one (k : ℕ)
    (hk : k ∈ ({12, 16, 18, 20, 22, 26} : Finset ℕ)) :
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    (∀ n : ℕ, ((σ₀ k n - b 1 n) / N').den.Coprime N') ∧
      ∀ n : ℕ, 1 ≤ n → ((σ₀ k n - b 1 n) / N').den.Coprime N'

/-- **Lu's two-term congruence for $G_k$.** Let $k \in \{24, 28, 30, 32, 34, 38\}$.
For $w, n \in \mathbb{N}$ let $\sigma_{-1}(n)$ be $1$ if $n = 0$ and $0$ otherwise; for $w \ge 1$
let $\sigma_{w-1}(0) = -B_w/(2w)$, where $B_w$ is the $w$-th Bernoulli number, and
$\sigma_{w-1}(n) = \sum_{d \mid n} d^{w-1}$ for $n \ge 1$. In $\mathbb{Q}[[q]]$ let
$G_w = \sum_{n \ge 0} \sigma_{w-1}(n) q^n$, let $E_w = G_w/\sigma_{w-1}(0)$ for even $w$, and let
$\Delta = q \prod_{j \ge 1} (1 - q^j)^{24}$; for $i, n \in \mathbb{N}$ write $b_i(n)$ for the
coefficient of $q^n$ in $\Delta^i E_{k-12i}$. Let $N_w = 1$ for $w \le 2$, let $N_w$ be the
absolute value of the numerator of $\sigma_{w-1}(0)$ for $w \ge 3$, and let $N'_k$ be the largest
divisor of $N_k$ that is coprime to $N_{k-12i}$ for every $1 \le i \le \lfloor k/12 \rfloor$. For
rationals $x, y$ and a positive integer $N$, $x \equiv y \pmod{N}$ means that $(x - y)/N$ has
denominator coprime to $N$. Let
$\gamma_2 = 2^{k-1} + 25 - 1/\sigma_{k-13}(0)$. Then
$\sigma_{k-1}(n) \equiv b_1(n) + \gamma_2 b_2(n) \pmod{N'_k}$ for every $n \ge 0$, that is,
$G_k \equiv \Delta E_{k-12} + \gamma_2 \Delta^2 E_{k-24} \pmod{N'_k}$ coefficientwise; in
particular the congruence holds for every $n \ge 1$.

Source: Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of
Integer Sequences 29 (2026), Article 26.5.1, Corollary 6 (`jis-2026-26.5.1-cor-6`). -/
public theorem_wanted eisenstein_congr_delta_mul_eisenstein_dim_two (k : ℕ)
    (hk : k ∈ ({24, 28, 30, 32, 34, 38} : Finset ℕ)) :
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let γ₂ : ℚ := 2 ^ (k - 1) + 25 - 1 / σ₀ (k - 12) 0
    (∀ n : ℕ, ((σ₀ k n - (b 1 n + γ₂ * b 2 n)) / N').den.Coprime N') ∧
      ∀ n : ℕ, 1 ≤ n → ((σ₀ k n - (b 1 n + γ₂ * b 2 n)) / N').den.Coprime N'

/-- **Lu's three-term congruence for $G_k$.** Let $k \in \{36, 40, 42, 44, 46, 50\}$.
For $w, n \in \mathbb{N}$ let $\sigma_{-1}(n)$ be $1$ if $n = 0$ and $0$ otherwise; for $w \ge 1$
let $\sigma_{w-1}(0) = -B_w/(2w)$, where $B_w$ is the $w$-th Bernoulli number, and
$\sigma_{w-1}(n) = \sum_{d \mid n} d^{w-1}$ for $n \ge 1$. In $\mathbb{Q}[[q]]$ let
$G_w = \sum_{n \ge 0} \sigma_{w-1}(n) q^n$, let $E_w = G_w/\sigma_{w-1}(0)$ for even $w$, and let
$\Delta = q \prod_{j \ge 1} (1 - q^j)^{24}$; for $i, n \in \mathbb{N}$ write $b_i(n)$ for the
coefficient of $q^n$ in $\Delta^i E_{k-12i}$. Let $N_w = 1$ for $w \le 2$, let $N_w$ be the
absolute value of the numerator of $\sigma_{w-1}(0)$ for $w \ge 3$, and let $N'_k$ be the largest
divisor of $N_k$ that is coprime to $N_{k-12i}$ for every $1 \le i \le \lfloor k/12 \rfloor$. For
rationals $x, y$ and a positive integer $N$, $x \equiv y \pmod{N}$ means that $(x - y)/N$ has
denominator coprime to $N$. Let
$\gamma_2 = 2^{k-1} + 25 - 1/\sigma_{k-13}(0)$ and
$\gamma_3 = 3^{k-1} + 48 \cdot 2^{k-1} + 949 - (2^{k-13} + 25)/\sigma_{k-13}(0) -
(2^{k-1} + 25)/\sigma_{k-25}(0) + 1/\bigl(\sigma_{k-13}(0)\,\sigma_{k-25}(0)\bigr)$. Then
$\sigma_{k-1}(n) \equiv b_1(n) + \gamma_2 b_2(n) + \gamma_3 b_3(n) \pmod{N'_k}$ for every
$n \ge 0$, that is,
$G_k \equiv \Delta E_{k-12} + \gamma_2 \Delta^2 E_{k-24} + \gamma_3 \Delta^3 E_{k-36}
\pmod{N'_k}$ coefficientwise; in particular the congruence holds for every $n \ge 1$.

Source: Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of
Integer Sequences 29 (2026), Article 26.5.1, Corollary 7 (`jis-2026-26.5.1-cor-7`). -/
public theorem_wanted eisenstein_congr_delta_mul_eisenstein_dim_three (k : ℕ)
    (hk : k ∈ ({36, 40, 42, 44, 46, 50} : Finset ℕ)) :
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let γ₂ : ℚ := 2 ^ (k - 1) + 25 - 1 / σ₀ (k - 12) 0
    let γ₃ : ℚ := 3 ^ (k - 1) + 2 ^ (k - 1) * 48 + 949 - (2 ^ (k - 13) + 25) / σ₀ (k - 12) 0 -
      (2 ^ (k - 1) + 25) / σ₀ (k - 24) 0 + 1 / (σ₀ (k - 12) 0 * σ₀ (k - 24) 0)
    (∀ n : ℕ, ((σ₀ k n - (b 1 n + γ₂ * b 2 n + γ₃ * b 3 n)) / N').den.Coprime N') ∧
      ∀ n : ℕ, 1 ≤ n → ((σ₀ k n - (b 1 n + γ₂ * b 2 n + γ₃ * b 3 n)) / N').den.Coprime N'

end

end MetaMathlibExt
