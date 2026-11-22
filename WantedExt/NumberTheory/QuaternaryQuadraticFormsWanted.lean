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

/-- Alaca and Altiary's formulas, reproved elementarily by Vasuki and Nagendra: for `n ≥ 1`,
`N(1,1,10,10;n)` and `N(2,2,5,5;n)` equal the same divisor-sum combination
`(2/3)σ(n) - (2/3)σ(n/2) + (4/3)σ(n/4) + (10/3)σ(n/5) - (16/3)σ(n/8) - (10/3)σ(n/10)
+ (20/3)σ(n/20) - (80/3)σ(n/40)` plus `(10/3)b₁(n) + (8/3)b₂(n) + 4b₃(n)`, respectively
`-(2/3)b₁(n) + (8/3)b₂(n) - 4b₃(n)`, where `∑ b₁(n)qⁿ = η₂²η₁₀²`, `∑ b₂(n)qⁿ = η₄²η₂₀²` and
`∑ b₃(n)qⁿ = η₄⁵η₁₀η₄₀² / (η₂η₈²η₂₀)`. The coefficient sequences are hypotheses pinned
by their generating functions on `‖q‖ < 1`.

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

/-- Alaca's formulas, reproved elementarily by Vasuki and Nagendra: for `n ≥ 1`, with
`S(n) = (2/3)σ(n) - (4/3)σ(n/2) + (8/3)σ(n/4) - 2σ(n/3) + 4σ(n/6) - 8σ(n/12) + (10/3)σ(n/5)
- (20/3)σ(n/10) + (40/3)σ(n/20) - 10σ(n/15) + 20σ(n/30) - 40σ(n/60)`,
`N(1,1,15,15;n) = S(n) + (2/3)(a₁ - 2a₂ + 4a₃ + 4a₄ + 8a₅)(n)`,
`N(3,3,5,5;n) = S(n) + (2/3)(-5a₁ - 14a₂ - 20a₃ + 4a₄ + 8a₅)(n)` and
`N(1,3,5,15;n) = (1/2)(σ(n) - 2σ(n/2) + 4σ(n/4) + 3σ(n/3) - 6σ(n/6) + 12σ(n/12) - 5σ(n/5)
+ 10σ(n/10) - 20σ(n/20) - 15σ(n/15) + 30σ(n/30) - 60σ(n/60)) + (3/2)a₁(n) + a₂(n) + 6a₃(n)`,
where `∑ a₁(n)qⁿ = η₁η₃η₅η₁₅`, `∑ a₂(n)qⁿ = η₂η₆η₁₀η₃₀`, `∑ a₃(n)qⁿ = η₄η₁₂η₂₀η₆₀`,
`∑ a₄(n)qⁿ = η₃η₅η₆η₁₀` and `∑ a₅(n)qⁿ = η₆η₁₀η₁₂η₂₀`, pinned as hypotheses on `‖q‖ < 1`.

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

/-- For `‖q‖ < 1`, `φ²(q)φ²(q¹⁰) + 5φ²(q²)φ²(q⁵) = φ⁴(q²) + 5φ⁴(q¹⁰) + 4qψ⁴(q²)
+ 20q⁵ψ⁴(q¹⁰) + 16q² f₄²f₂₀² - 16q³ f₄⁵f₁₀f₄₀² / (f₂f₈²f₂₀)`. The power `q³` of the last
term (the eta quotient `η₄⁵η₁₀η₄₀²/(η₂η₈²η₂₀)` of Theorem 1.1) is not legible in the
available text of the paper; it is the one consistent with Theorem 1.1 and with
Equation (3.13).

Source: K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25
(2025), Article A24, Lemma 3.1. -/
public theorem_wanted phi_sq_phi_sq_ten_add_five_phi_sq_two_phi_sq_five
    (q : ℂ) (hq : ‖q‖ < 1) :
    (φ q) ^ 2 * (φ (q ^ 10)) ^ 2 + 5 * (φ (q ^ 2)) ^ 2 * (φ (q ^ 5)) ^ 2 =
      (φ (q ^ 2)) ^ 4 + 5 * (φ (q ^ 10)) ^ 4 + 4 * q * (ψ (q ^ 2)) ^ 4
        + 20 * q ^ 5 * (ψ (q ^ 10)) ^ 4 + 16 * q ^ 2 * (𝔣 (q ^ 4)) ^ 2 * (𝔣 (q ^ 20)) ^ 2
        - 16 * q ^ 3 * ((𝔣 (q ^ 4)) ^ 5 * 𝔣 (q ^ 10) * (𝔣 (q ^ 40)) ^ 2
          / (𝔣 (q ^ 2) * (𝔣 (q ^ 8)) ^ 2 * 𝔣 (q ^ 20)))

/-- For `‖q‖ < 1`, Equation (3.13):
`φ²(q)φ²(q¹⁰) = -(1/36)[P₁ - P₂ + 2P₄ + 5P₅ - 8P₈ - 5P₁₀ + 10P₂₀ - 40P₄₀]
+ (10/3)q f₂²f₁₀² + (8/3)q² f₄²f₂₀² + 4q³ f₄⁵f₁₀f₄₀² / (f₂f₈²f₂₀)`.

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

/-- For `‖q‖ < 1`, Equation (3.14):
`φ²(q²)φ²(q⁵) = -(1/36)[P₁ - P₂ + 2P₄ + 5P₅ - 8P₈ - 5P₁₀ + 10P₂₀ - 40P₄₀]
- (2/3)q f₂²f₁₀² + (8/3)q² f₄²f₂₀² - 4q³ f₄⁵f₁₀f₄₀² / (f₂f₈²f₂₀)`.

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

/-- For `‖q‖ < 1`, `12φ²(q)φ²(q¹⁰) + 12φ²(q²)φ²(q⁵) = φ⁴(q) + 5φ⁴(q⁵) + 4φ⁴(q²) + 20φ⁴(q¹⁰)
- φ⁴(-q) - 5φ⁴(-q⁵) + 32q f₂²f₁₀² + 64q² f₄²f₂₀²`.

Source: K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25
(2025), Article A24, Lemma 3.2. -/
public theorem_wanted twelve_phi_sq_phi_sq_ten_add_twelve_phi_sq_two_phi_sq_five
    (q : ℂ) (hq : ‖q‖ < 1) :
    12 * (φ q) ^ 2 * (φ (q ^ 10)) ^ 2 + 12 * (φ (q ^ 2)) ^ 2 * (φ (q ^ 5)) ^ 2 =
      (φ q) ^ 4 + 5 * (φ (q ^ 5)) ^ 4 + 4 * (φ (q ^ 2)) ^ 4 + 20 * (φ (q ^ 10)) ^ 4
        - (φ (-q)) ^ 4 - 5 * (φ (-q ^ 5)) ^ 4
        + 32 * q * (𝔣 (q ^ 2)) ^ 2 * (𝔣 (q ^ 10)) ^ 2
        + 64 * q ^ 2 * (𝔣 (q ^ 4)) ^ 2 * (𝔣 (q ^ 20)) ^ 2

/-- For `‖q‖ < 1`, `φ²(q)φ²(q¹⁵) = -(1/36)[P₁ - 2P₂ - 3P₃ + 4P₄ + 5P₅ + 6P₆ - 10P₁₀ - 12P₁₂
- 15P₁₅ + 20P₂₀ + 30P₃₀ - 60P₆₀] + (2/3)[q f₁f₃f₅f₁₅ - 2q² f₂f₆f₁₀f₃₀ + 4q⁴ f₄f₁₂f₂₀f₆₀
+ 4q f₃f₅f₆f₁₀ + 8q² f₆f₁₀f₁₂f₂₀]`.

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

/-- For `‖q‖ < 1`, with Ramanujan's `f(q) = (-q;-q)_∞`,
`q f(q)f(q³)f(q⁵)f(q¹⁵) = q f₁f₃f₅f₁₅ + 2q² f₂f₆f₁₀f₃₀ + 4q⁴ f₄f₁₂f₂₀f₆₀`.

Source: K. R. Vasuki and P. Nagendra, *On Certain Quaternary Quadratic Forms*, INTEGERS 25
(2025), Article A24, Lemma 4.3. -/
public theorem_wanted q_mul_ramanujanF_one_three_five_fifteen (q : ℂ) (hq : ‖q‖ < 1) :
    q * 𝔣 (-q) * 𝔣 (-q ^ 3) * 𝔣 (-q ^ 5) * 𝔣 (-q ^ 15) =
      q * 𝔣 q * 𝔣 (q ^ 3) * 𝔣 (q ^ 5) * 𝔣 (q ^ 15)
        + 2 * q ^ 2 * 𝔣 (q ^ 2) * 𝔣 (q ^ 6) * 𝔣 (q ^ 10) * 𝔣 (q ^ 30)
        + 4 * q ^ 4 * 𝔣 (q ^ 4) * 𝔣 (q ^ 12) * 𝔣 (q ^ 20) * 𝔣 (q ^ 60)

/-- For `‖q‖ < 1`, `φ²(q³)φ²(q⁵) = -(1/36)[P₁ - 2P₂ - 3P₃ + 4P₄ + 5P₅ + 6P₆ - 10P₁₀ - 12P₁₂
- 15P₁₅ + 20P₂₀ + 30P₃₀ - 60P₆₀] - (2/3)[5q f₁f₃f₅f₁₅ + 14q² f₂f₆f₁₀f₃₀ + 20q⁴ f₄f₁₂f₂₀f₆₀
- 4q f₃f₅f₆f₁₀ - 8q² f₆f₁₀f₁₂f₂₀]`.

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

/-- For `‖q‖ < 1`, `φ(q)φ(q³)φ(q⁵)φ(q¹⁵) = -(1/48)[P₁ - 2P₂ + 3P₃ + 4P₄ - 5P₅ - 6P₆ + 10P₁₀
+ 12P₁₂ - 15P₁₅ - 20P₂₀ + 30P₃₀ - 60P₆₀] + (3/2)q f₁f₃f₅f₁₅ + q² f₂f₆f₁₀f₃₀
+ 6q⁴ f₄f₁₂f₂₀f₆₀`.

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
