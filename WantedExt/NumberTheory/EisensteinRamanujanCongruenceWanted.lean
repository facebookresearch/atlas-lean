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

/-- **Theorem 1.** For even `k ≥ 12`, `k ≠ 14`, with `m = dim S_k` (`⌊k/12⌋ - 1` if
`k ≡ 2 (mod 12)`, else `⌊k/12⌋`), `C = (c_{ij})`, `c_{ij} = (τ^{*i} * σ_{k-12i-1})(j) / σ_{k-12i-1}(0)`
(the `q^j`-coefficient of `Δ^i E_{k-12i}`), and `(γ_1, …, γ_m) = (σ_{k-1}(1), …, σ_{k-1}(m)) C⁻¹`:
`G_k ≡ ∑_{i=1}^m γ_i Δ^i E_{k-12i} (mod N'_k)`, coefficientwise for every `n ≥ 0`.

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

/-- **Corollary 3.** With the notation of Theorem 1, for all `n ≥ 1`,
`σ_{k-1}(n) ≡ ∑_{i=1}^m (γ_i / σ_{k-12i-1}(0)) (τ^{*i} * σ_{k-12i-1})(n) (mod N'_k)`.

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

/-- **Corollary 5.** For `k ∈ {12, 16, 18, 20, 22, 26}`, `G_k ≡ Δ E_{k-12} (mod N'_k)`
(coefficientwise, all `n ≥ 0`) and `σ_{k-1}(n) ≡ (τ * σ_{k-13})(n) / σ_{k-13}(0) (mod N'_k)`
for `n ≥ 1` (notation of Theorem 1).

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

/-- **Corollary 6.** For `k ∈ {24, 28, 30, 32, 34, 38}`, with
`γ_2 = 2^{k-1} + 25 - 1/σ_{k-13}(0)`: `G_k ≡ Δ E_{k-12} + γ_2 Δ^2 E_{k-24} (mod N'_k)`
(coefficientwise, all `n ≥ 0`) and, for `n ≥ 1`,
`σ_{k-1}(n) ≡ (τ * σ_{k-13})(n)/σ_{k-13}(0) + γ_2 (τ * τ * σ_{k-25})(n)/σ_{k-25}(0) (mod N'_k)`
(notation of Theorem 1).

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

/-- **Corollary 7.** For `k ∈ {36, 40, 42, 44, 46, 50}`, with
`γ_2 = 2^{k-1} + 25 - 1/σ_{k-13}(0)` and
`γ_3 = 3^{k-1} + 48·2^{k-1} + 949 - (2^{k-13} + 25)/σ_{k-13}(0) - (2^{k-1} + 25)/σ_{k-25}(0)
+ 1/(σ_{k-13}(0) σ_{k-25}(0))`:
`G_k ≡ Δ E_{k-12} + γ_2 Δ^2 E_{k-24} + γ_3 Δ^3 E_{k-36} (mod N'_k)` (coefficientwise, all
`n ≥ 0`) and the corresponding congruence for `σ_{k-1}(n)`, `n ≥ 1` (notation of Theorem 1).

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
