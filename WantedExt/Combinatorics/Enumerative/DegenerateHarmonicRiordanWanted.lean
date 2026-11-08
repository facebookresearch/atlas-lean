/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generalized degenerate harmonic numbers and Riordan arrays

Statements from Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic
Numbers and Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41.

Throughout, `λ > 0` and `α > 0` are real, `(x)_{n,λ} = x(x - λ)⋯(x - (n - 1)λ)` is the existing
`MetaMathlibExt.generalizedFallingFactorial x λ n` (over `ℝ`), the degenerate
exponential is `e_λ(t) = ∑ (1)_{n,λ} tⁿ / n!`, and `-log_λ(1 - t/α) = ∑_{k ≥ 1} (-1)^{k-1}
binom(λ, k) tᵏ / (λ αᵏ)` (paper, Equations (1) and (2)). The degenerate Bernoulli, Euler, Stirling
and Daehee numbers are defined through the generating functions (6)-(9) of the paper, as power
series coefficients.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.HsuShiueGeneralizedStirlingNumber

namespace MetaMathlibExt

@[expose] public section

/-- The coefficient `(-1)^{n-1} binom(λ, n) / (λ αⁿ)` of `tⁿ` in `-log_λ(1 - t/α)`, set to `0` at
`n = 0` (the series has no constant term). This is the paper's `H⁰_{n,λ}(α)` for `n ≥ 1`; at
`n = 0` the value `0` follows the paper's convention `H^r_{0,λ}(α) = 0` and the generating function.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1
(`H⁰_{n,λ}(α)` and Equation (2)). -/
noncomputable def degenerateHarmonicTerm (lam α : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (-1) ^ (n - 1) * Ring.choose lam n / (lam * α ^ n)

/-- `degenerateHarmonicTerm λ α 0 = 0`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem degenerateHarmonicTerm_zero (lam α : ℝ) : degenerateHarmonicTerm lam α 0 = 0 := by
  simp [degenerateHarmonicTerm]

/-- `degenerateHarmonicTerm λ α 1 = 1 / α` for `λ ≠ 0`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem degenerateHarmonicTerm_one {lam : ℝ} (hlam : lam ≠ 0) (α : ℝ) :
    degenerateHarmonicTerm lam α 1 = 1 / α := by
  simp [degenerateHarmonicTerm]
  field_simp

/-- Dağlı's generalized degenerate harmonic numbers
`H_{n,λ}(α) = ∑_{k=1}^n (-1)^{k-1} binom(λ, k) / (λ αᵏ)`, with `H_{0,λ}(α) = 0`. At `α = 1` these
are the degenerate harmonic numbers `H_{n,λ}`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
noncomputable def generalizedDegenerateHarmonic (lam α : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (-1) ^ (k - 1) * Ring.choose lam k / (lam * α ^ k)

/-- `H_{0,λ}(α) = 0`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem generalizedDegenerateHarmonic_zero (lam α : ℝ) :
    generalizedDegenerateHarmonic lam α 0 = 0 := by
  simp [generalizedDegenerateHarmonic]

/-- `H_{n+1,λ}(α) = H_{n,λ}(α) + (-1)ⁿ binom(λ, n + 1) / (λ α^{n+1})`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem generalizedDegenerateHarmonic_succ (lam α : ℝ) (n : ℕ) :
    generalizedDegenerateHarmonic lam α (n + 1) =
      generalizedDegenerateHarmonic lam α n +
        (-1) ^ n * Ring.choose lam (n + 1) / (lam * α ^ (n + 1)) := by
  simp [generalizedDegenerateHarmonic, Finset.sum_Icc_succ_top (Nat.le_add_left 1 n)]

/-- Generalized degenerate hyperharmonic numbers of order `r`: `H⁰_{n,λ}(α)` is
`degenerateHarmonicTerm`, and `H^{r+1}_{n,λ}(α) = ∑_{k=1}^n H^r_{k,λ}(α)`, so `H^r_{0,λ}(α) = 0`
for `r ≥ 1` and `H¹_{n,λ}(α) = H_{n,λ}(α)`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
noncomputable def generalizedDegenerateHyperharmonic (lam α : ℝ) : ℕ → ℕ → ℝ
  | 0, n => degenerateHarmonicTerm lam α n
  | r + 1, n => ∑ k ∈ Finset.Icc 1 n, generalizedDegenerateHyperharmonic lam α r k

/-- `H^{r+1}_{0,λ}(α) = 0`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem generalizedDegenerateHyperharmonic_succ_zero (lam α : ℝ) (r : ℕ) :
    generalizedDegenerateHyperharmonic lam α (r + 1) 0 = 0 := by
  simp [generalizedDegenerateHyperharmonic]

/-- `H¹_{n,λ}(α) = H_{n,λ}(α)`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem generalizedDegenerateHyperharmonic_one (lam α : ℝ) (n : ℕ) :
    generalizedDegenerateHyperharmonic lam α 1 n = generalizedDegenerateHarmonic lam α n := by
  simp only [generalizedDegenerateHyperharmonic, generalizedDegenerateHarmonic]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.1 hk).1; omega
  simp [degenerateHarmonicTerm, hk0]

/-- Generalized degenerate harmonic numbers of rank `r`, through their generating function
`(-log_λ(1 - t/α))^{r+1} / (1 - t) = ∑ H_λ(n, r, α) tⁿ` (paper, Equation (5)): `H_λ(n, r, α)` is
the sum of the coefficients of `t⁰, …, tⁿ` in `(-log_λ(1 - t/α))^{r+1}`. This agrees with the
paper's explicit sum over `k₀, …, k_r ≥ 1` with `k₀ + ⋯ + k_r ≤ n`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1,
Equation (5). -/
noncomputable def degenerateHarmonicRank (lam α : ℝ) (n r : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1),
    PowerSeries.coeff m (PowerSeries.mk (degenerateHarmonicTerm lam α) ^ (r + 1))

/-- `H_λ(0, r, α) = 0`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem degenerateHarmonicRank_zero_left (lam α : ℝ) (r : ℕ) :
    degenerateHarmonicRank lam α 0 r = 0 := by
  simp [degenerateHarmonicRank, PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
    degenerateHarmonicTerm_zero]

/-- `H_λ(n, 0, α) = H_{n,λ}(α)`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem degenerateHarmonicRank_zero_right (lam α : ℝ) (n : ℕ) :
    degenerateHarmonicRank lam α n 0 = generalizedDegenerateHarmonic lam α n := by
  induction n with
  | zero => simp [degenerateHarmonicRank_zero_left, generalizedDegenerateHarmonic_zero]
  | succ n ih =>
    rw [generalizedDegenerateHarmonic_succ, ← ih]
    simp [degenerateHarmonicRank, Finset.sum_range_succ _ (n + 1), degenerateHarmonicTerm]

/-- The degenerate exponential series `e_λ(t) = ∑ (1)_{n,λ} tⁿ / n!`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (1) at
`x = 1`. -/
noncomputable def degenerateExpSeries (lam : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => generalizedFallingFactorial 1 lam n / n.factorial

/-- The constant term of `e_λ(t)` is `1`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (1). -/
theorem constantCoeff_degenerateExpSeries (lam : ℝ) :
    PowerSeries.constantCoeff (degenerateExpSeries lam) = 1 := by
  simp [degenerateExpSeries, generalizedFallingFactorial]

/-- Degenerate Bernoulli numbers `β_{n,λ}`: `t / (e_λ(t) - 1) = ∑ β_{n,λ} tⁿ / n!` (paper,
Equation (6) at `x = 0`), i.e. `n!` times the `tⁿ` coefficient of the inverse of
`(e_λ(t) - 1) / t = ∑ (1)_{n+1,λ} tⁿ / (n + 1)!`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (6). -/
noncomputable def degenerateBernoulli (lam : ℝ) (n : ℕ) : ℝ :=
  n.factorial * PowerSeries.coeff n
    (PowerSeries.mk fun m => generalizedFallingFactorial 1 lam (m + 1) / (m + 1).factorial)⁻¹

/-- `β_{0,λ} = 1`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (6). -/
theorem degenerateBernoulli_zero (lam : ℝ) : degenerateBernoulli lam 0 = 1 := by
  simp [degenerateBernoulli, PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.constantCoeff_inv, generalizedFallingFactorial]

/-- Degenerate Euler numbers `ε_{n,λ}`: `2 / (e_λ(t) + 1) = ∑ ε_{n,λ} tⁿ / n!` (paper,
Equation (7) at `x = 0`).

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (7). -/
noncomputable def degenerateEuler (lam : ℝ) (n : ℕ) : ℝ :=
  n.factorial * PowerSeries.coeff n (PowerSeries.C (2 : ℝ) * (degenerateExpSeries lam + 1)⁻¹)

/-- `ε_{0,λ} = 1`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (7). -/
theorem degenerateEuler_zero (lam : ℝ) : degenerateEuler lam 0 = 1 := by
  simp [degenerateEuler, PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_inv,
    constantCoeff_degenerateExpSeries]
  norm_num

/-- Degenerate Stirling numbers of the first kind:
`(log_λ(1 + t))ᵏ / k! = ∑_{n ≥ k} S_{1,λ}(n, k) tⁿ / n!` (paper, Equation (8)), with
`log_λ(1 + t) = ∑_{n ≥ 1} binom(λ, n) tⁿ / λ` (paper, Equation (2)).

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equations (2) and (8). -/
noncomputable def degenerateStirlingFirst (lam : ℝ) (n k : ℕ) : ℝ :=
  n.factorial / k.factorial * PowerSeries.coeff n
    ((PowerSeries.mk fun m => if m = 0 then 0 else Ring.choose lam m / lam) ^ k)

/-- `S_{1,λ}(n, 0) = [n = 0]`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (8). -/
theorem degenerateStirlingFirst_zero_right (lam : ℝ) (n : ℕ) :
    degenerateStirlingFirst lam n 0 = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0 <;> simp [degenerateStirlingFirst, PowerSeries.coeff_one, hn]

/-- Degenerate Stirling numbers of the second kind:
`(e_λ(t) - 1)ᵏ / k! = ∑_{n ≥ k} S_{2,λ}(n, k) tⁿ / n!` (paper, Equation (8)).

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (8). -/
noncomputable def degenerateStirlingSecond (lam : ℝ) (n k : ℕ) : ℝ :=
  n.factorial / k.factorial * PowerSeries.coeff n ((degenerateExpSeries lam - 1) ^ k)

/-- `S_{2,λ}(n, 0) = [n = 0]`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (8). -/
theorem degenerateStirlingSecond_zero_right (lam : ℝ) (n : ℕ) :
    degenerateStirlingSecond lam n 0 = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0 <;> simp [degenerateStirlingSecond, PowerSeries.coeff_one, hn]

/-- Degenerate Daehee numbers `D_{n,λ} = n! binom(λ, n + 1) / λ`: by Equation (2),
`log_λ(1 + t) / t = ∑ binom(λ, n + 1) tⁿ / λ`, so this is the paper's definition (9) at `x = 0`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equations (2)
and (9). -/
noncomputable def degenerateDaehee (lam : ℝ) (n : ℕ) : ℝ :=
  n.factorial * Ring.choose lam (n + 1) / lam

/-- `D_{0,λ} = 1` for `λ ≠ 0`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (9). -/
theorem degenerateDaehee_zero {lam : ℝ} (hlam : lam ≠ 0) : degenerateDaehee lam 0 = 1 := by
  simp [degenerateDaehee, hlam]

/-- Theorem 1: for `n ≥ 0`,
`∑_{k=0}^n (-1)ᵏ H^{k+1}_{n-k+1,λ}(α) = (-1)ⁿ D_{n,λ} / (α^{n+1} n!)`, and for `r ≥ 0`,
`∑_{k=0}^n binom(k + r, r) H_{n-k+1,λ}(α) = H^{r+2}_{n+1,λ}(α)`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 1
(`integers-2024-A41-thm-1`). -/
public theorem_wanted degenerateHyperharmonic_alternating_and_binomial_sums {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * generalizedDegenerateHyperharmonic lam α (k + 1) (n - k + 1) =
      (-1) ^ n * degenerateDaehee lam n / (α ^ (n + 1) * n.factorial) ∧
    ∀ r : ℕ, ∑ k ∈ Finset.range (n + 1),
        ((k + r).choose r : ℝ) * generalizedDegenerateHarmonic lam α (n - k + 1) =
      generalizedDegenerateHyperharmonic lam α (r + 2) (n + 1)

/-- Theorem 2: for `n ≥ 1`,
`∑_{k=0}^n (-1)^{k+1} binom(n, k) H_{k,λ} = binom(n + λ - 1, n) / λ`, where
`H_{k,λ} = H_{k,λ}(1)` are the degenerate harmonic numbers.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 2
(`integers-2024-A41-thm-2`). -/
public theorem_wanted degenerateHarmonic_alternating_binomial_sum {lam : ℝ} (hlam : 0 < lam) {n : ℕ}
    (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ (k + 1) * (n.choose k : ℝ) * generalizedDegenerateHarmonic lam 1 k =
      Ring.choose ((n : ℝ) + lam - 1) n / lam

/-- Theorem 3: for `n ≥ 0`,
`∑_{k=0}^n (-1)ᵏ (1)_{k,λ} / k! · H_λ(n + 1, k, α) = H_{n+1,λ}(α) - H_{n,λ}(α) / α`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 3
(`integers-2024-A41-thm-3`). -/
public theorem_wanted degenerateHarmonicRank_exp_weighted_sum {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α)
    (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * generalizedFallingFactorial 1 lam k / k.factorial *
          degenerateHarmonicRank lam α (n + 1) k =
      generalizedDegenerateHarmonic lam α (n + 1) - generalizedDegenerateHarmonic lam α n / α

/-- Theorem 4: for `n, r ≥ 0`,
`∑_{k=0}^n H_λ(k, r + 1, α) = ∑_{k=0}^n H_{n-k,λ}(α) H_λ(k, r, α)`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 4
(`integers-2024-A41-thm-4`). -/
public theorem_wanted degenerateHarmonicRank_succ_partial_sum {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α)
    (n r : ℕ) :
    ∑ k ∈ Finset.range (n + 1), degenerateHarmonicRank lam α k (r + 1) =
      ∑ k ∈ Finset.range (n + 1),
        generalizedDegenerateHarmonic lam α (n - k) * degenerateHarmonicRank lam α k r

/-- Theorem 5: for `n ≥ 0`,
`∑_{k=0}^n (-1)ᵏ (1)_{k+1,λ} / (k + 1)! · H_λ(n + 1, k, α) = 1 / α`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 5
(`integers-2024-A41-thm-5`). -/
public theorem_wanted degenerateHarmonicRank_shifted_exp_weighted_sum {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * generalizedFallingFactorial 1 lam (k + 1) / (k + 1).factorial *
          degenerateHarmonicRank lam α (n + 1) k =
      1 / α

/-- Theorem 6: for `0 ≤ r ≤ n`,
`∑_{k=r}^n (-1)^{n-k} binom(λ, n - k + 1) / (λ α^{n-k+1}) · binom(k, r) = H^{r+1}_{n-r+1,λ}(α)`.
The hypothesis `r ≤ n` makes the summation range `r ≤ k ≤ n` nonempty, as in the paper.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 6
(`integers-2024-A41-thm-6`). -/
public theorem_wanted degenerateHyperharmonic_eq_binomial_sum {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α)
    {n r : ℕ} (hrn : r ≤ n) :
    ∑ k ∈ Finset.Icc r n,
        (-1 : ℝ) ^ (n - k) * Ring.choose lam (n - k + 1) / (lam * α ^ (n - k + 1)) *
          (k.choose r : ℝ) =
      generalizedDegenerateHyperharmonic lam α (r + 1) (n - r + 1)

/-- Theorem 7: for `n ≥ 1`,
`∑_{k=1}^n (1)_{k,λ} / k! · H_λ(n, k - 1, α) =
  ∑_{k=1}^n ∑_{i=1}^k (-1)^{k+i} (1)_{i,λ} S_{1,λ}(k, i) / (αᵏ k!)`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 7
(`integers-2024-A41-thm-7`). -/
public theorem_wanted degenerateHarmonicRank_exp_sum_eq_stirlingFirst {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n,
        generalizedFallingFactorial 1 lam k / k.factorial * degenerateHarmonicRank lam α n (k - 1) =
      ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Icc 1 k,
        (-1 : ℝ) ^ (k + i) * generalizedFallingFactorial 1 lam i * degenerateStirlingFirst lam k i /
          (α ^ k * k.factorial)

/-- Theorem 8: for `n ≥ 1`,
`∑_{k=1}^n (-1)ᵏ β_{k,λ} H_λ(n, k - 1, α) / k! = α H_{n+1,λ}(α) - 1`, and for `α ≠ 1/2`,
`∑_{k=1}^n (-1)^{k+1} ε_{k,λ} / k! · H_λ(n, k - 1, α) = ((2α)^{-n} - 1) / (2α - 1)`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 8
(`integers-2024-A41-thm-8`). -/
public theorem_wanted degenerateHarmonicRank_bernoulli_euler_sums {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ k * degenerateBernoulli lam k * degenerateHarmonicRank lam α n (k - 1) /
          k.factorial =
      α * generalizedDegenerateHarmonic lam α (n + 1) - 1 ∧
    (α ≠ 1 / 2 →
      ∑ k ∈ Finset.Icc 1 n,
          (-1 : ℝ) ^ (k + 1) * degenerateEuler lam k / k.factorial *
            degenerateHarmonicRank lam α n (k - 1) =
        (((2 * α) ^ n)⁻¹ - 1) / (2 * α - 1))

/-- Theorem 9: for `1 ≤ m ≤ n`,
`∑_{k=m}^n (-1)ᵏ S_{2,λ}(k, m) H_λ(n, k - 1, α) / k! = (-1)ᵐ / (m! αᵐ)`.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 9
(`integers-2024-A41-thm-9`). -/
public theorem_wanted degenerateHarmonicRank_stirlingSecond_sum {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑ k ∈ Finset.Icc m n,
        (-1 : ℝ) ^ k * degenerateStirlingSecond lam k m * degenerateHarmonicRank lam α n (k - 1) /
          k.factorial =
      (-1) ^ m / (m.factorial * α ^ m)

end

end MetaMathlibExt
