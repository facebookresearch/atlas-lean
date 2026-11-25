/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan

/-!
# Quaternary forms `x² + y² + 10z² + 10w²`, `x² + y² + 15z² + 15w²`, …: wishlist

Source: K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*,
INTEGERS 25 (2025), Article A24.

No new definition is introduced. The paper's notation is written inline (local notation):
`N(a,b,c,d;n)` is the number of `(x₁,x₂,x₃,x₄) ∈ ℤ⁴` with `a x₁² + b x₂² + c x₃² + d x₄² = n`;
`σ(n/k)` is `σ(n/k)` when `k ∣ n` and `0` otherwise; `f_k = (q^k;q^k)_∞` is
`qPochhammerInfRaw (q^k) (q^k)`; Ramanujan's `φ(q) = f(q,q) = ∑_{n ∈ ℤ} q^{n²}` is
`ramanujanThetaRaw q q`; Ramanujan's `ψ(q) = f(q,q³) = ∑_{n ≥ 0} q^{n(n+1)/2}` is
`ramanujanThetaRaw q (q ^ 3)`; and `P_k = P(q^k)` with
`P(q) = 1 - 24 ∑_{m ≥ 1} m q^m / (1 - q^m)`. The cusp-form coefficients `aᵢ(n)`, `bᵢ(n)`
of the paper's eta quotients are taken as sequences characterised by their generating
functions on the unit disk, where `η_k = q^{k/24} f_k`.
-/

open scoped ArithmeticFunction.sigma

namespace MetaMathlibExt

@[expose] public section

/-- `N(a,b,c,d;n)`: the number of integer solutions of `a x₁² + b x₂² + c x₃² + d x₄² = n`,
as a complex number. -/
local notation "𝐍" a:max b:max c:max d:max n:max =>
  ((Set.ncard (Set.ofPred fun x : Fin 4 → ℤ =>
    (a : ℤ) * x 0 ^ 2 + (b : ℤ) * x 1 ^ 2 + (c : ℤ) * x 2 ^ 2 + (d : ℤ) * x 3 ^ 2 = (n : ℤ)) :
      ℕ) : ℂ)
/-- `σ(n / k)`, which is `0` unless `k ∣ n`. -/
local notation "σdiv" k:max n:max =>
  (if k ∣ n then ((σ 1 (n / k) : ℕ) : ℂ) else 0)
/-- `f_k = (x;x)_∞` at `x = q^k`. -/
local notation "𝔣" x:max => QPochhammer.qPochhammerInfRaw x x
/-- Ramanujan's `φ(x) = f(x,x) = ∑_{n ∈ ℤ} x^{n²}`. -/
local notation "φ" x:max => ramanujanThetaRaw x x
/-- Ramanujan's `ψ(x) = f(x,x³) = ∑_{n ≥ 0} x^{n(n+1)/2}`. -/
local notation "ψ" x:max => ramanujanThetaRaw x (x ^ 3)
/-- The weight-two Eisenstein series `P(x) = 1 - 24 ∑_{m ≥ 1} m x^m / (1 - x^m)`. -/
local notation "𝐏" x:max =>
  (1 - 24 * tsum fun m : ℕ => ((m + 1 : ℕ) : ℂ) * x ^ (m + 1) / (1 - x ^ (m + 1)))

/-- **Representation numbers of the quaternary forms $(1,1,10,10)$ and $(2,2,5,5)$.**
For a complex number $q$ write $f_k = \prod_{m \ge 1} (1 - q^{km})$. For
integers $a, b, c, d$ and $n$, let $N(a,b,c,d;n)$ be the number of $(x_1, x_2, x_3, x_4) \in
\mathbb{Z}^4$ with $a x_1^2 + b x_2^2 + c x_3^2 + d x_4^2 = n$, and let $\sigma(n/k)$ be the sum
of the positive divisors of $n/k$ if $k \mid n$ and $0$ otherwise. Let $b_1, b_2, b_3$ be sequences
of complex numbers indexed by $n \ge 0$ such that for every complex $q$ with $|q| < 1$ the
series $\sum_{n \ge 0} b_i(n) q^n$ converge, with sums $q f_2^2 f_{10}^2$, $q^2 f_4^2 f_{20}^2$
and $q^3 f_4^5 f_{10} f_{40}^2 / (f_2 f_8^2 f_{20})$ for $i = 1, 2, 3$ respectively. For
$n \ge 1$ put
$$
T(n) = \tfrac{2}{3}\sigma(n) - \tfrac{2}{3}\sigma(n/2) + \tfrac{4}{3}\sigma(n/4) +
\tfrac{10}{3}\sigma(n/5) - \tfrac{16}{3}\sigma(n/8) - \tfrac{10}{3}\sigma(n/10) +
\tfrac{20}{3}\sigma(n/20) - \tfrac{80}{3}\sigma(n/40).
$$
Then for every $n \ge 1$,
$$
N(1,1,10,10;n) = T(n) + \tfrac{10}{3} b_1(n) + \tfrac{8}{3} b_2(n) + 4b_3(n)
$$
and
$$
N(2,2,5,5;n) = T(n) - \tfrac{2}{3} b_1(n) + \tfrac{8}{3} b_2(n) - 4b_3(n).
$$

With $\eta_k = q^{k/24} f_k$, the three generating functions are the eta quotients
$\eta_2^2\eta_{10}^2$, $\eta_4^2\eta_{20}^2$ and
$\eta_4^5\eta_{10}\eta_{40}^2/(\eta_2\eta_8^2\eta_{20})$. These formulas are due to Alaca and
Altiary; Vasuki and Nagendra reprove them elementarily.

Source: K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25
(2025), Article A24, Theorem 1.1 (Alaca and Altiary). -/
public theorem_wanted quaternaryRep_one_one_ten_ten_and_two_two_five_five
    (b₁ b₂ b₃ : ℕ → ℂ)
    (hb₁ : ∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun n => b₁ n * q ^ n) (q * (𝔣 (q ^ 2)) ^ 2 * (𝔣 (q ^ 10)) ^ 2))
    (hb₂ : ∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun n => b₂ n * q ^ n) (q ^ 2 * (𝔣 (q ^ 4)) ^ 2 * (𝔣 (q ^ 20)) ^ 2))
    (hb₃ : ∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun n => b₃ n * q ^ n)
        (q ^ 3 * (𝔣 (q ^ 4)) ^ 5 * 𝔣 (q ^ 10) * (𝔣 (q ^ 40)) ^ 2 /
          (𝔣 (q ^ 2) * (𝔣 (q ^ 8)) ^ 2 * 𝔣 (q ^ 20))))
    (n : ℕ) (hn : 0 < n) :
    𝐍 1 1 10 10 n =
        2 / 3 * σdiv 1 n - 2 / 3 * σdiv 2 n + 4 / 3 * σdiv 4 n + 10 / 3 * σdiv 5 n
          - 16 / 3 * σdiv 8 n - 10 / 3 * σdiv 10 n + 20 / 3 * σdiv 20 n - 80 / 3 * σdiv 40 n
          + 10 / 3 * b₁ n + 8 / 3 * b₂ n + 4 * b₃ n ∧
      𝐍 2 2 5 5 n =
        2 / 3 * σdiv 1 n - 2 / 3 * σdiv 2 n + 4 / 3 * σdiv 4 n + 10 / 3 * σdiv 5 n
          - 16 / 3 * σdiv 8 n - 10 / 3 * σdiv 10 n + 20 / 3 * σdiv 20 n - 80 / 3 * σdiv 40 n
          - 2 / 3 * b₁ n + 8 / 3 * b₂ n - 4 * b₃ n

/-- **Representation numbers of the quaternary forms $(1,1,15,15)$, $(3,3,5,5)$ and
$(1,3,5,15)$.** For a complex number $q$ write $f_k = \prod_{m \ge 1} (1 - q^{km})$. For
integers $a, b, c, d$ and $n$, let $N(a,b,c,d;n)$ be the number of $(x_1, x_2, x_3, x_4) \in
\mathbb{Z}^4$ with $a x_1^2 + b x_2^2 + c x_3^2 + d x_4^2 = n$, and let $\sigma(n/k)$ be the sum
of the positive divisors of $n/k$ if $k \mid n$ and $0$ otherwise. Let $a_1, \dots, a_5$ be
sequences of complex numbers indexed by $n \ge 0$ such that for every complex $q$ with
$|q| < 1$ the series $\sum_{n \ge 0} a_i(n) q^n$ converge, with sums $q f_1 f_3 f_5 f_{15}$,
$q^2 f_2 f_6 f_{10} f_{30}$, $q^4 f_4 f_{12} f_{20} f_{60}$, $q f_3 f_5 f_6 f_{10}$ and
$q^2 f_6 f_{10} f_{12} f_{20}$ for $i = 1, \dots, 5$ respectively. For $n \ge 1$ put
$$
S(n) = \tfrac{2}{3}\sigma(n) - \tfrac{4}{3}\sigma(n/2) + \tfrac{8}{3}\sigma(n/4) - 2\sigma(n/3) +
4\sigma(n/6) - 8\sigma(n/12) + \tfrac{10}{3}\sigma(n/5) - \tfrac{20}{3}\sigma(n/10) +
\tfrac{40}{3}\sigma(n/20) - 10\sigma(n/15) + 20\sigma(n/30) - 40\sigma(n/60).
$$
Then for every $n \ge 1$,
$$
N(1,1,15,15;n) = S(n) + \tfrac{2}{3}(a_1(n) - 2a_2(n) + 4a_3(n) + 4a_4(n) + 8a_5(n)),
$$
$$
N(3,3,5,5;n) = S(n) + \tfrac{2}{3}(-5a_1(n) - 14a_2(n) - 20a_3(n) + 4a_4(n) + 8a_5(n))
$$
and
$$
N(1,3,5,15;n) = \tfrac{1}{2}(\sigma(n) - 2\sigma(n/2) + 4\sigma(n/4) + 3\sigma(n/3) -
6\sigma(n/6) + 12\sigma(n/12) - 5\sigma(n/5) + 10\sigma(n/10) - 20\sigma(n/20) -
15\sigma(n/15) + 30\sigma(n/30) - 60\sigma(n/60)) + \tfrac{3}{2} a_1(n) + a_2(n) + 6a_3(n).
$$

With $\eta_k = q^{k/24} f_k$, the five generating functions are the eta quotients
$\eta_1\eta_3\eta_5\eta_{15}$, $\eta_2\eta_6\eta_{10}\eta_{30}$,
$\eta_4\eta_{12}\eta_{20}\eta_{60}$, $\eta_3\eta_5\eta_6\eta_{10}$ and
$\eta_6\eta_{10}\eta_{12}\eta_{20}$. These formulas are due to Alaca; Vasuki and Nagendra
reprove them elementarily.

Source: K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25
(2025), Article A24, Theorem 1.2 (Alaca). -/
public theorem_wanted quaternaryRep_one_one_fifteen_fifteen_three_three_five_five_one_three_five_fifteen
    (a₁ a₂ a₃ a₄ a₅ : ℕ → ℂ)
    (ha₁ : ∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun n => a₁ n * q ^ n) (q * 𝔣 q * 𝔣 (q ^ 3) * 𝔣 (q ^ 5) * 𝔣 (q ^ 15)))
    (ha₂ : ∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun n => a₂ n * q ^ n)
        (q ^ 2 * 𝔣 (q ^ 2) * 𝔣 (q ^ 6) * 𝔣 (q ^ 10) * 𝔣 (q ^ 30)))
    (ha₃ : ∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun n => a₃ n * q ^ n)
        (q ^ 4 * 𝔣 (q ^ 4) * 𝔣 (q ^ 12) * 𝔣 (q ^ 20) * 𝔣 (q ^ 60)))
    (ha₄ : ∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun n => a₄ n * q ^ n) (q * 𝔣 (q ^ 3) * 𝔣 (q ^ 5) * 𝔣 (q ^ 6) * 𝔣 (q ^ 10)))
    (ha₅ : ∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun n => a₅ n * q ^ n)
        (q ^ 2 * 𝔣 (q ^ 6) * 𝔣 (q ^ 10) * 𝔣 (q ^ 12) * 𝔣 (q ^ 20)))
    (n : ℕ) (hn : 0 < n) :
    𝐍 1 1 15 15 n =
        2 / 3 * σdiv 1 n - 4 / 3 * σdiv 2 n + 8 / 3 * σdiv 4 n - 2 * σdiv 3 n
          + 4 * σdiv 6 n - 8 * σdiv 12 n + 10 / 3 * σdiv 5 n - 20 / 3 * σdiv 10 n
          + 40 / 3 * σdiv 20 n - 10 * σdiv 15 n + 20 * σdiv 30 n - 40 * σdiv 60 n
          + 2 / 3 * (a₁ n - 2 * a₂ n + 4 * a₃ n + 4 * a₄ n + 8 * a₅ n) ∧
      𝐍 3 3 5 5 n =
        2 / 3 * σdiv 1 n - 4 / 3 * σdiv 2 n + 8 / 3 * σdiv 4 n - 2 * σdiv 3 n
          + 4 * σdiv 6 n - 8 * σdiv 12 n + 10 / 3 * σdiv 5 n - 20 / 3 * σdiv 10 n
          + 40 / 3 * σdiv 20 n - 10 * σdiv 15 n + 20 * σdiv 30 n - 40 * σdiv 60 n
          + 2 / 3 * (-5 * a₁ n - 14 * a₂ n - 20 * a₃ n + 4 * a₄ n + 8 * a₅ n) ∧
      𝐍 1 3 5 15 n =
        1 / 2 * (σdiv 1 n - 2 * σdiv 2 n + 4 * σdiv 4 n + 3 * σdiv 3 n - 6 * σdiv 6 n
            + 12 * σdiv 12 n - 5 * σdiv 5 n + 10 * σdiv 10 n - 20 * σdiv 20 n
            - 15 * σdiv 15 n + 30 * σdiv 30 n - 60 * σdiv 60 n)
          + 3 / 2 * a₁ n + a₂ n + 6 * a₃ n

/-- **A theta identity for $\varphi(q)^2\varphi(q^{10})^2 + 5\varphi(q^2)^2\varphi(q^5)^2$.**
Let $q$ be a complex number with $|q| < 1$. Write $\varphi(x) = \sum_{n \in \mathbb{Z}} x^{n^2}$
and $\psi(x) = \sum_{n \ge 0} x^{n(n+1)/2}$ for Ramanujan's theta functions, and
$f_k = \prod_{m \ge 1} (1 - q^{km})$. Then
$$
\varphi(q)^2\varphi(q^{10})^2 + 5\varphi(q^2)^2\varphi(q^5)^2 = \varphi(q^2)^4 +
5\varphi(q^{10})^4 + 4q\psi(q^2)^4 + 20q^5\psi(q^{10})^4 + 16q^2 f_4^2 f_{20}^2 -
16q^3 \frac{f_4^5 f_{10} f_{40}^2}{f_2 f_8^2 f_{20}}.
$$

The power $q^3$ of the last term is not legible in the available text of the paper; it is the
one consistent with Theorem 1.1 and with Equation (3.13).

Source: K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25
(2025), Article A24, Lemma 3.1. -/
public theorem_wanted phi_sq_phi_sq_ten_add_five_phi_sq_two_phi_sq_five
    (q : ℂ) (hq : ‖q‖ < 1) :
    (φ q) ^ 2 * (φ (q ^ 10)) ^ 2 + 5 * (φ (q ^ 2)) ^ 2 * (φ (q ^ 5)) ^ 2 =
      (φ (q ^ 2)) ^ 4 + 5 * (φ (q ^ 10)) ^ 4 + 4 * q * (ψ (q ^ 2)) ^ 4
        + 20 * q ^ 5 * (ψ (q ^ 10)) ^ 4 + 16 * q ^ 2 * (𝔣 (q ^ 4)) ^ 2 * (𝔣 (q ^ 20)) ^ 2
        - 16 * q ^ 3 * ((𝔣 (q ^ 4)) ^ 5 * 𝔣 (q ^ 10) * (𝔣 (q ^ 40)) ^ 2
          / (𝔣 (q ^ 2) * (𝔣 (q ^ 8)) ^ 2 * 𝔣 (q ^ 20)))

/-- **Eisenstein-series formula for $\varphi(q)^2\varphi(q^{10})^2$.** Let $q$ be
a complex number with $|q| < 1$. Write $\varphi(x) = \sum_{n \in \mathbb{Z}} x^{n^2}$ for
Ramanujan's theta function, $f_k = \prod_{m \ge 1} (1 - q^{km})$, and $P_k = P(q^k)$, where
$P(x) = 1 - 24 \sum_{m \ge 1} m x^m / (1 - x^m)$ is the weight-two Eisenstein series. Then
$$
\varphi(q)^2\varphi(q^{10})^2 = -\tfrac{1}{36}(P_1 - P_2 + 2P_4 + 5P_5 - 8P_8 - 5P_{10} + 10P_{20} -
40P_{40}) + \tfrac{10}{3} q f_2^2 f_{10}^2 + \tfrac{8}{3} q^2 f_4^2 f_{20}^2 +
4q^3 \frac{f_4^5 f_{10} f_{40}^2}{f_2 f_8^2 f_{20}}.
$$

Source: K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25
(2025), Article A24, Lemma 3.3, Equation (3.13). -/
public theorem_wanted phi_sq_mul_phi_sq_ten_eisenstein (q : ℂ) (hq : ‖q‖ < 1) :
    (φ q) ^ 2 * (φ (q ^ 10)) ^ 2 =
      -(1 / 36) * (𝐏 q - 𝐏 (q ^ 2) + 2 * 𝐏 (q ^ 4) + 5 * 𝐏 (q ^ 5) - 8 * 𝐏 (q ^ 8)
          - 5 * 𝐏 (q ^ 10) + 10 * 𝐏 (q ^ 20) - 40 * 𝐏 (q ^ 40))
        + 10 / 3 * q * (𝔣 (q ^ 2)) ^ 2 * (𝔣 (q ^ 10)) ^ 2
        + 8 / 3 * q ^ 2 * (𝔣 (q ^ 4)) ^ 2 * (𝔣 (q ^ 20)) ^ 2
        + 4 * q ^ 3 * ((𝔣 (q ^ 4)) ^ 5 * 𝔣 (q ^ 10) * (𝔣 (q ^ 40)) ^ 2
          / (𝔣 (q ^ 2) * (𝔣 (q ^ 8)) ^ 2 * 𝔣 (q ^ 20)))

/-- **Eisenstein-series formula for $\varphi(q^2)^2\varphi(q^5)^2$.** Let $q$ be
a complex number with $|q| < 1$. Write $\varphi(x) = \sum_{n \in \mathbb{Z}} x^{n^2}$ for
Ramanujan's theta function, $f_k = \prod_{m \ge 1} (1 - q^{km})$, and $P_k = P(q^k)$, where
$P(x) = 1 - 24 \sum_{m \ge 1} m x^m / (1 - x^m)$ is the weight-two Eisenstein series. Then
$$
\varphi(q^2)^2\varphi(q^5)^2 = -\tfrac{1}{36}(P_1 - P_2 + 2P_4 + 5P_5 - 8P_8 - 5P_{10} + 10P_{20} -
40P_{40}) - \tfrac{2}{3} q f_2^2 f_{10}^2 + \tfrac{8}{3} q^2 f_4^2 f_{20}^2 -
4q^3 \frac{f_4^5 f_{10} f_{40}^2}{f_2 f_8^2 f_{20}}.
$$

Source: K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25
(2025), Article A24, Lemma 3.3, Equation (3.14). -/
public theorem_wanted phi_sq_two_mul_phi_sq_five_eisenstein (q : ℂ) (hq : ‖q‖ < 1) :
    (φ (q ^ 2)) ^ 2 * (φ (q ^ 5)) ^ 2 =
      -(1 / 36) * (𝐏 q - 𝐏 (q ^ 2) + 2 * 𝐏 (q ^ 4) + 5 * 𝐏 (q ^ 5) - 8 * 𝐏 (q ^ 8)
          - 5 * 𝐏 (q ^ 10) + 10 * 𝐏 (q ^ 20) - 40 * 𝐏 (q ^ 40))
        - 2 / 3 * q * (𝔣 (q ^ 2)) ^ 2 * (𝔣 (q ^ 10)) ^ 2
        + 8 / 3 * q ^ 2 * (𝔣 (q ^ 4)) ^ 2 * (𝔣 (q ^ 20)) ^ 2
        - 4 * q ^ 3 * ((𝔣 (q ^ 4)) ^ 5 * 𝔣 (q ^ 10) * (𝔣 (q ^ 40)) ^ 2
          / (𝔣 (q ^ 2) * (𝔣 (q ^ 8)) ^ 2 * 𝔣 (q ^ 20)))

/-- **A theta identity for $12\varphi(q)^2\varphi(q^{10})^2 + 12\varphi(q^2)^2\varphi(q^5)^2$.**
Let $q$ be a complex number with $|q| < 1$. Write $\varphi(x) = \sum_{n \in \mathbb{Z}} x^{n^2}$
for Ramanujan's theta function and $f_k = \prod_{m \ge 1} (1 - q^{km})$. Then
$$
12\varphi(q)^2\varphi(q^{10})^2 + 12\varphi(q^2)^2\varphi(q^5)^2 = \varphi(q)^4 + 5\varphi(q^5)^4 +
4\varphi(q^2)^4 + 20\varphi(q^{10})^4 - \varphi(-q)^4 - 5\varphi(-q^5)^4 +
32q f_2^2 f_{10}^2 + 64q^2 f_4^2 f_{20}^2.
$$

Source: K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25
(2025), Article A24, Lemma 3.2. -/
public theorem_wanted twelve_phi_sq_phi_sq_ten_add_twelve_phi_sq_two_phi_sq_five
    (q : ℂ) (hq : ‖q‖ < 1) :
    12 * (φ q) ^ 2 * (φ (q ^ 10)) ^ 2 + 12 * (φ (q ^ 2)) ^ 2 * (φ (q ^ 5)) ^ 2 =
      (φ q) ^ 4 + 5 * (φ (q ^ 5)) ^ 4 + 4 * (φ (q ^ 2)) ^ 4 + 20 * (φ (q ^ 10)) ^ 4
        - (φ (-q)) ^ 4 - 5 * (φ (-q ^ 5)) ^ 4
        + 32 * q * (𝔣 (q ^ 2)) ^ 2 * (𝔣 (q ^ 10)) ^ 2
        + 64 * q ^ 2 * (𝔣 (q ^ 4)) ^ 2 * (𝔣 (q ^ 20)) ^ 2

/-- **Eisenstein-series formula for $\varphi(q)^2\varphi(q^{15})^2$.** Let $q$ be
a complex number with $|q| < 1$. Write $\varphi(x) = \sum_{n \in \mathbb{Z}} x^{n^2}$ for
Ramanujan's theta function, $f_k = \prod_{m \ge 1} (1 - q^{km})$, and $P_k = P(q^k)$, where
$P(x) = 1 - 24 \sum_{m \ge 1} m x^m / (1 - x^m)$ is the weight-two Eisenstein series. Then
$$
\varphi(q)^2\varphi(q^{15})^2 = -\tfrac{1}{36}(P_1 - 2P_2 - 3P_3 + 4P_4 + 5P_5 + 6P_6 - 10P_{10} -
12P_{12} - 15P_{15} + 20P_{20} + 30P_{30} - 60P_{60}) + \tfrac{2}{3}(q f_1 f_3 f_5 f_{15} -
2q^2 f_2 f_6 f_{10} f_{30} + 4q^4 f_4 f_{12} f_{20} f_{60} + 4q f_3 f_5 f_6 f_{10} +
8q^2 f_6 f_{10} f_{12} f_{20}).
$$

Source: K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25
(2025), Article A24, Lemma 4.2. -/
public theorem_wanted phi_sq_mul_phi_sq_fifteen_eisenstein (q : ℂ) (hq : ‖q‖ < 1) :
    (φ q) ^ 2 * (φ (q ^ 15)) ^ 2 =
      -(1 / 36) * (𝐏 q - 2 * 𝐏 (q ^ 2) - 3 * 𝐏 (q ^ 3) + 4 * 𝐏 (q ^ 4) + 5 * 𝐏 (q ^ 5)
          + 6 * 𝐏 (q ^ 6) - 10 * 𝐏 (q ^ 10) - 12 * 𝐏 (q ^ 12) - 15 * 𝐏 (q ^ 15)
          + 20 * 𝐏 (q ^ 20) + 30 * 𝐏 (q ^ 30) - 60 * 𝐏 (q ^ 60))
        + 2 / 3 * (q * 𝔣 q * 𝔣 (q ^ 3) * 𝔣 (q ^ 5) * 𝔣 (q ^ 15)
          - 2 * q ^ 2 * 𝔣 (q ^ 2) * 𝔣 (q ^ 6) * 𝔣 (q ^ 10) * 𝔣 (q ^ 30)
          + 4 * q ^ 4 * 𝔣 (q ^ 4) * 𝔣 (q ^ 12) * 𝔣 (q ^ 20) * 𝔣 (q ^ 60)
          + 4 * q * 𝔣 (q ^ 3) * 𝔣 (q ^ 5) * 𝔣 (q ^ 6) * 𝔣 (q ^ 10)
          + 8 * q ^ 2 * 𝔣 (q ^ 6) * 𝔣 (q ^ 10) * 𝔣 (q ^ 12) * 𝔣 (q ^ 20))

/-- **A product identity for Ramanujan's $f(q)f(q^3)f(q^5)f(q^{15})$.** Let $q$ be a complex
number with $|q| < 1$. Write $f_k = \prod_{m \ge 1} (1 - q^{km})$, and let
$f(x) = \prod_{m \ge 1} (1 - (-x)^m) = (-x; -x)_\infty$ be Ramanujan's function. Then
$$
q f(q) f(q^3) f(q^5) f(q^{15}) = q f_1 f_3 f_5 f_{15} + 2q^2 f_2 f_6 f_{10} f_{30} +
4q^4 f_4 f_{12} f_{20} f_{60}.
$$

Source: K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25
(2025), Article A24, Lemma 4.3. -/
public theorem_wanted q_mul_ramanujanF_one_three_five_fifteen (q : ℂ) (hq : ‖q‖ < 1) :
    q * 𝔣 (-q) * 𝔣 (-q ^ 3) * 𝔣 (-q ^ 5) * 𝔣 (-q ^ 15) =
      q * 𝔣 q * 𝔣 (q ^ 3) * 𝔣 (q ^ 5) * 𝔣 (q ^ 15)
        + 2 * q ^ 2 * 𝔣 (q ^ 2) * 𝔣 (q ^ 6) * 𝔣 (q ^ 10) * 𝔣 (q ^ 30)
        + 4 * q ^ 4 * 𝔣 (q ^ 4) * 𝔣 (q ^ 12) * 𝔣 (q ^ 20) * 𝔣 (q ^ 60)

/-- **Eisenstein-series formula for $\varphi(q^3)^2\varphi(q^5)^2$.** Let $q$ be
a complex number with $|q| < 1$. Write $\varphi(x) = \sum_{n \in \mathbb{Z}} x^{n^2}$ for
Ramanujan's theta function, $f_k = \prod_{m \ge 1} (1 - q^{km})$, and $P_k = P(q^k)$, where
$P(x) = 1 - 24 \sum_{m \ge 1} m x^m / (1 - x^m)$ is the weight-two Eisenstein series. Then
$$
\varphi(q^3)^2\varphi(q^5)^2 = -\tfrac{1}{36}(P_1 - 2P_2 - 3P_3 + 4P_4 + 5P_5 + 6P_6 - 10P_{10} -
12P_{12} - 15P_{15} + 20P_{20} + 30P_{30} - 60P_{60}) - \tfrac{2}{3}(5q f_1 f_3 f_5 f_{15} +
14q^2 f_2 f_6 f_{10} f_{30} + 20q^4 f_4 f_{12} f_{20} f_{60} - 4q f_3 f_5 f_6 f_{10} -
8q^2 f_6 f_{10} f_{12} f_{20}).
$$

Source: K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25
(2025), Article A24, Lemma 4.4. -/
public theorem_wanted phi_sq_three_mul_phi_sq_five_eisenstein (q : ℂ) (hq : ‖q‖ < 1) :
    (φ (q ^ 3)) ^ 2 * (φ (q ^ 5)) ^ 2 =
      -(1 / 36) * (𝐏 q - 2 * 𝐏 (q ^ 2) - 3 * 𝐏 (q ^ 3) + 4 * 𝐏 (q ^ 4) + 5 * 𝐏 (q ^ 5)
          + 6 * 𝐏 (q ^ 6) - 10 * 𝐏 (q ^ 10) - 12 * 𝐏 (q ^ 12) - 15 * 𝐏 (q ^ 15)
          + 20 * 𝐏 (q ^ 20) + 30 * 𝐏 (q ^ 30) - 60 * 𝐏 (q ^ 60))
        - 2 / 3 * (5 * q * 𝔣 q * 𝔣 (q ^ 3) * 𝔣 (q ^ 5) * 𝔣 (q ^ 15)
          + 14 * q ^ 2 * 𝔣 (q ^ 2) * 𝔣 (q ^ 6) * 𝔣 (q ^ 10) * 𝔣 (q ^ 30)
          + 20 * q ^ 4 * 𝔣 (q ^ 4) * 𝔣 (q ^ 12) * 𝔣 (q ^ 20) * 𝔣 (q ^ 60)
          - 4 * q * 𝔣 (q ^ 3) * 𝔣 (q ^ 5) * 𝔣 (q ^ 6) * 𝔣 (q ^ 10)
          - 8 * q ^ 2 * 𝔣 (q ^ 6) * 𝔣 (q ^ 10) * 𝔣 (q ^ 12) * 𝔣 (q ^ 20))

/-- **Eisenstein-series formula for $\varphi(q)\varphi(q^3)\varphi(q^5)\varphi(q^{15})$.** Let $q$
be a complex number with $|q| < 1$. Write $\varphi(x) = \sum_{n \in \mathbb{Z}} x^{n^2}$ for
Ramanujan's theta function, $f_k = \prod_{m \ge 1} (1 - q^{km})$, and $P_k = P(q^k)$, where
$P(x) = 1 - 24 \sum_{m \ge 1} m x^m / (1 - x^m)$ is the weight-two Eisenstein series. Then
$$
\varphi(q)\varphi(q^3)\varphi(q^5)\varphi(q^{15}) = -\tfrac{1}{48}(P_1 - 2P_2 + 3P_3 + 4P_4 -
5P_5 - 6P_6 + 10P_{10} + 12P_{12} - 15P_{15} - 20P_{20} + 30P_{30} - 60P_{60}) +
\tfrac{3}{2} q f_1 f_3 f_5 f_{15} + q^2 f_2 f_6 f_{10} f_{30} + 6q^4 f_4 f_{12} f_{20} f_{60}.
$$

Source: K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25
(2025), Article A24, Lemma 4.6. -/
public theorem_wanted phi_mul_phi_three_mul_phi_five_mul_phi_fifteen_eisenstein
    (q : ℂ) (hq : ‖q‖ < 1) :
    φ q * φ (q ^ 3) * φ (q ^ 5) * φ (q ^ 15) =
      -(1 / 48) * (𝐏 q - 2 * 𝐏 (q ^ 2) + 3 * 𝐏 (q ^ 3) + 4 * 𝐏 (q ^ 4) - 5 * 𝐏 (q ^ 5)
          - 6 * 𝐏 (q ^ 6) + 10 * 𝐏 (q ^ 10) + 12 * 𝐏 (q ^ 12) - 15 * 𝐏 (q ^ 15)
          - 20 * 𝐏 (q ^ 20) + 30 * 𝐏 (q ^ 30) - 60 * 𝐏 (q ^ 60))
        + 3 / 2 * q * 𝔣 q * 𝔣 (q ^ 3) * 𝔣 (q ^ 5) * 𝔣 (q ^ 15)
        + q ^ 2 * 𝔣 (q ^ 2) * 𝔣 (q ^ 6) * 𝔣 (q ^ 10) * 𝔣 (q ^ 30)
        + 6 * q ^ 4 * 𝔣 (q ^ 4) * 𝔣 (q ^ 12) * 𝔣 (q ^ 20) * 𝔣 (q ^ 60)

end

end MetaMathlibExt
