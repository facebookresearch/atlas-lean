/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.RingTheory.Binomial

/-!
# Symmetric identities on modified degenerate Bernoulli polynomials

Statements from Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4.

The modified degenerate Bernoulli polynomial of Dolgy, Kim, Kwon and Seo is defined in the paper by
`∑ 𝔅_{n,λ}(x) tⁿ / n! = t (1+λ)^{xt/λ} / ((1+λ)^{t/λ} - 1)`. With the principal branch
`(1+λ)^w = exp (w log (1+λ))` and `c = log (1+λ) / λ` this generating function is
`t e^{cxt} / (e^{ct} - 1)`, whence `𝔅_{n,λ}(x) = c^{n-1} B_n(x)`; this closed form is the definition
below, and `modifiedDegenerateBernoulli_generating_function` proves the paper's generating function
from it. The generating function needs `λ ≠ 0` and `λ ≠ -1` (exactly the condition `c ≠ 0`), which
the statements assume. Binomial coefficients with a complex upper argument are `Ring.choose`.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

/-- The modified degenerate Bernoulli polynomial `𝔅_{n,λ}(x) = c^{n-1} B_n(x)` with
`c = log (1+λ) / λ` (principal branch), where `B_n` is the Bernoulli polynomial
(`Polynomial.bernoulli`, with `B_1(x) = x - 1/2`).

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Section 1 (generating
function of Dolgy, Kim, Kwon and Seo). -/
noncomputable def modifiedDegenerateBernoulli (lam : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  (Complex.log (1 + lam) / lam) ^ ((n : ℤ) - 1) * Polynomial.aeval x (Polynomial.bernoulli n)

/-- The paper's generating function: with `c = log (1+λ) / λ ≠ 0`,
`(∑ 𝔅_{n,λ}(x) tⁿ / n!) · (e^{ct} - 1) = t e^{cxt}`, i.e.
`(∑ 𝔅_{n,λ}(x) tⁿ / n!) · ((1+λ)^{t/λ} - 1) = t (1+λ)^{xt/λ}`.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Section 1. -/
theorem modifiedDegenerateBernoulli_generating_function (lam x : ℂ)
    (h : Complex.log (1 + lam) / lam ≠ 0) :
    PowerSeries.mk (fun n => modifiedDegenerateBernoulli lam n x / n.factorial) *
        (PowerSeries.rescale (Complex.log (1 + lam) / lam) (PowerSeries.exp ℂ) - 1) =
      PowerSeries.X *
        PowerSeries.rescale (Complex.log (1 + lam) / lam * x) (PowerSeries.exp ℂ) := by
  set c := Complex.log (1 + lam) / lam with hc
  have key := congrArg (PowerSeries.rescale c)
    (Polynomial.bernoulli_generating_function (A := ℂ) x)
  rw [map_mul, map_sub, map_one, map_mul, PowerSeries.rescale_X, PowerSeries.rescale_rescale] at key
  have hmk : PowerSeries.mk (fun n => modifiedDegenerateBernoulli lam n x / n.factorial) =
      PowerSeries.C c⁻¹ * PowerSeries.rescale c (PowerSeries.mk fun n =>
        Polynomial.aeval x ((1 / n.factorial : ℚ) • Polynomial.bernoulli n)) := by
    ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
      PowerSeries.coeff_mk, map_smul, modifiedDegenerateBernoulli, zpow_sub₀ h, zpow_one,
      zpow_natCast, Rat.smul_def]
    push_cast
    field_simp
  rw [hmk, mul_assoc, key, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h, map_one,
    one_mul, mul_comm x c]

/-- `𝔅_{1,λ}(x) = x - 1/2`.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Section 1. -/
theorem modifiedDegenerateBernoulli_one (lam x : ℂ) :
    modifiedDegenerateBernoulli lam 1 x = x - 1 / 2 := by
  simp [modifiedDegenerateBernoulli, Polynomial.bernoulli_one]

/-- Theorem 1: for integers `m ≥ 2`, `n ≥ 1`, complex `r_1, …, r_m`, `x_1, …, x_m` and
`r₀ = n - r_1 - ⋯ - r_m`,
`r₀ ∑_{k_1+⋯+k_m=n} ∏_j C(r_j, k_j) 𝔅_{k_j,λ}(x_j) = -∑_i r_i ∑_{k_1+⋯+k_m=n} C(r₀, k_i)
𝔅_{k_i,λ}(1 - x_i) ∏_{j ≠ i} C(r_j, k_j) 𝔅_{k_j,λ}(x_j - x_i + 1_{j>i})`, for `λ ≠ 0, -1`.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Theorem 1
(`jis-2024-24.5.4-thm-1`). -/
public theorem_wanted modifiedDegenerateBernoulli_symmetric_identity (m n : ℕ) (hm : 2 ≤ m)
    (hn : 1 ≤ n) (r x : Fin m → ℂ) (lam : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ((n : ℂ) - ∑ j, r j) * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        ∏ j, Ring.choose (r j) (k j) * modifiedDegenerateBernoulli lam (k j) (x j) =
      -∑ i, r i * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        Ring.choose ((n : ℂ) - ∑ j, r j) (k i) * modifiedDegenerateBernoulli lam (k i) (1 - x i) *
          ∏ j ∈ univ.erase i, Ring.choose (r j) (k j) *
            modifiedDegenerateBernoulli lam (k j) (x j - x i + if i < j then 1 else 0)

/-- Corollary 2, three-term identity: with
`𝔇_{s,t,λ}(x, y) = ∑_{k=0}^n (-1)^k C(s, k) C(t, n-k) 𝔅_{n-k,λ}(x) 𝔅_{k,λ}(y)`, for `n ≥ 1`,
`r + s + t = n` and `x + y + z = 1`,
`r 𝔇_{s,t,λ}(x, y) + s 𝔇_{t,r,λ}(y, z) + t 𝔇_{r,s,λ}(z, x) = 0`, for `λ ≠ 0, -1`.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Corollary 2, equation
(sunpanD) (`jis-2024-24.5.4-cor-2`). -/
public theorem_wanted modifiedDegenerateBernoulli_three_term (n : ℕ) (hn : 1 ≤ n) (lam : ℂ)
    (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) (r s t x y z : ℂ) (hrst : r + s + t = n)
    (hxyz : x + y + z = 1) :
    let D : ℂ → ℂ → ℂ → ℂ → ℂ := fun s t x y =>
      ∑ k ∈ range (n + 1), (-1) ^ k * Ring.choose s k * Ring.choose t (n - k) *
        modifiedDegenerateBernoulli lam (n - k) x * modifiedDegenerateBernoulli lam k y
    r * D s t x y + s * D t r y z + t * D r s z x = 0

/-- Corollary 2, Miki-type identity: for `n ≥ 4` and `𝔅_{k,λ} = 𝔅_{k,λ}(0)`,
`∑_{k=1}^{n-1} 𝔅_{k,λ} 𝔅_{n-k,λ} / k - ∑_{k=1}^{n-1} C(n, k) 𝔅_{k,λ} 𝔅_{n-k,λ} / k =
λ / log (1+λ) · H_n 𝔅_{n,λ} + n/2 · 𝔅_{n-1,λ}`, for `λ ≠ 0, -1`.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Corollary 2, equation
(mikiD) (`jis-2024-24.5.4-cor-2`). -/
public theorem_wanted modifiedDegenerateBernoulli_miki (n : ℕ) (hn : 4 ≤ n) (lam : ℂ)
    (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ∑ k ∈ Icc 1 (n - 1), modifiedDegenerateBernoulli lam k 0 / k *
        modifiedDegenerateBernoulli lam (n - k) 0 -
      ∑ k ∈ Icc 1 (n - 1), (n.choose k : ℂ) * modifiedDegenerateBernoulli lam k 0 / k *
        modifiedDegenerateBernoulli lam (n - k) 0 =
      lam / Complex.log (1 + lam) * (harmonic n : ℂ) * modifiedDegenerateBernoulli lam n 0 +
        n / 2 * modifiedDegenerateBernoulli lam (n - 1) 0

/-- Corollary 2, Matiyasevich-Dunne-Schubert-type identity: for `n ≥ 4` and
`𝔅_{k,λ} = 𝔅_{k,λ}(0)`, `(n+2) ∑_{k=2}^{n-2} 𝔅_{k,λ} 𝔅_{n-k,λ} =
2 ∑_{k=2}^{n-2} C(n+2, k) 𝔅_{k,λ} 𝔅_{n-k,λ} + λ / log (1+λ) · n(n+1) 𝔅_{n,λ}`, for `λ ≠ 0, -1`.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Corollary 2, equation
(matiyasevichD) (`jis-2024-24.5.4-cor-2`). -/
public theorem_wanted modifiedDegenerateBernoulli_matiyasevich (n : ℕ) (hn : 4 ≤ n) (lam : ℂ)
    (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ((n : ℂ) + 2) * ∑ k ∈ Icc 2 (n - 2),
        modifiedDegenerateBernoulli lam k 0 * modifiedDegenerateBernoulli lam (n - k) 0 =
      2 * ∑ k ∈ Icc 2 (n - 2), ((n + 2).choose k : ℂ) *
          modifiedDegenerateBernoulli lam k 0 * modifiedDegenerateBernoulli lam (n - k) 0 +
        lam / Complex.log (1 + lam) * (n * (n + 1)) * modifiedDegenerateBernoulli lam n 0

/-- Lemma 3: for `m ≥ 2` and nonnegative integers `s_1, …, s_m` with `S = s_1 + ⋯ + s_m`,
`∑_i s_i 𝔅_{s_i-1,λ}(x_i) ∏_{j ≠ i} 𝔅_{s_j,λ}(x_j) = ∑_i s_i ∑_{k_1+⋯+k_m=S} 𝔅_{k_i-1,λ}(x_i)
∏_{j ≠ i} C(s_j, k_j) 𝔅_{k_j,λ}(x_j - x_i + 1_{j>i})`, with the paper's convention
`𝔅_{-1,λ} = 0` (written as the `k_i = 0` case; on the left the factor `s_i` vanishes there), for
`λ ≠ 0, -1`.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Lemma 3
(`jis-2024-24.5.4-lem-3`). -/
public theorem_wanted modifiedDegenerateBernoulli_lemma_three (m : ℕ) (hm : 2 ≤ m)
    (s : Fin m → ℕ) (x : Fin m → ℂ) (lam : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ∑ i, (s i : ℂ) * modifiedDegenerateBernoulli lam (s i - 1) (x i) *
        ∏ j ∈ univ.erase i, modifiedDegenerateBernoulli lam (s j) (x j) =
      ∑ i, (s i : ℂ) * ∑ k ∈ Finset.Nat.antidiagonalTuple m (∑ j, s j),
        (if k i = 0 then 0 else modifiedDegenerateBernoulli lam (k i - 1) (x i)) *
          ∏ j ∈ univ.erase i, ((s j).choose (k j) : ℂ) *
            modifiedDegenerateBernoulli lam (k j) (x j - x i + if i < j then 1 else 0)

end

end MetaMathlibExt
