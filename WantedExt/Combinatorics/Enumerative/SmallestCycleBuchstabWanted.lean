/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Data.Fintype.Perm

/-!
# Gravel–Panario, smallest cycles and the (generalized) Buchstab function — wishlist

Statement-only records for Gravel and Panario, INTEGERS 24 (2024), Article A7
(source: arXiv:2212.12847v2 TeX). `X_n` is the length of the smallest cycle of
a uniformly random permutation of `Fin n`, written as
`⨅ x, Function.minimalPeriod σ x` (the cycle through `x` has length
`minimalPeriod σ x`); moments are averages over `Equiv.Perm (Fin n)`.

The Buchstab function `ω` and the generalized Buchstab function `Ω_K` enter as
hypotheses: any `ω : ℝ → ℝ` with `ω x = 1/x` on `[1, 2]` and
`x ω(x) = 1 + ∫_1^{x-1} ω` for `x ≥ 2` (the integrated form of
`(x ω(x))' = ω(x - 1)`), and any `Ω` with `Ω = 1` on `[1, 2)` and
`Ω(x) = 1 + K ∫_2^x Ω(u - 1)/(u - 1) du` for `x ≥ 2`. Both systems determine the
function on `[1, ∞)` interval by interval.
-/

open Real

namespace MetaMathlibExt

@[expose] public section

/-- Theorem 1, first part: `E(X_n) = e^{-γ} log n (1 + O(h(n)/log n))` for some
`h(n) = o(log n)`, stated in the equivalent form `E(X_n) / (e^{-γ} log n) → 1`.

Source: Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab
Function and Revisiting the Variance of the Distribution of the Smallest
Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 1
(`integers-2024-A7-thm-1`). -/
public theorem_wanted smallest_cycle_mean_asymp :
    Filter.Tendsto (fun n : ℕ =>
      ((∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ)) /
          (n.factorial : ℝ)) / (Real.exp (-eulerMascheroniConstant) * Real.log n))
      Filter.atTop (nhds 1)

/-- Theorem 1, second part: for integers `ℓ ≥ 2` there is `ε > 0` with
`E(X_n^ℓ) = ℓ n^{ℓ-1} (∫_1^∞ ω(x) / x^ℓ dx) (1 + O(n^{-ε}))`.

Source: Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab
Function and Revisiting the Variance of the Distribution of the Smallest
Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 1
(`integers-2024-A7-thm-1`). -/
public theorem_wanted smallest_cycle_moment_asymp (ω : ℝ → ℝ)
    (hω₁ : ∀ x ∈ Set.Icc (1 : ℝ) 2, ω x = 1 / x)
    (hω₂ : ∀ x : ℝ, 2 ≤ x → x * ω x = 1 + ∫ t in (1 : ℝ)..(x - 1), ω t)
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ∃ ε C : ℝ, 0 < ε ∧ ∀ n : ℕ, 1 ≤ n →
      |(∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ) ^ ℓ) /
            (n.factorial : ℝ) -
          ℓ * (n : ℝ) ^ (ℓ - 1) * ∫ x in Set.Ioi (1 : ℝ), ω x / x ^ ℓ|
        ≤ C * (n : ℝ) ^ (ℓ - 1) * (n : ℝ) ^ (-ε)

/-- Theorem 2: there is `ε > 0` with `Var(X_n) = n C (1 + O(n^{-ε}))`, where
`C = 2 ∫_1^∞ ω(x) / x^2 dx`.

Source: Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab
Function and Revisiting the Variance of the Distribution of the Smallest
Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 2
(`integers-2024-A7-thm-2`). -/
public theorem_wanted smallest_cycle_variance_asymp (ω : ℝ → ℝ)
    (hω₁ : ∀ x ∈ Set.Icc (1 : ℝ) 2, ω x = 1 / x)
    (hω₂ : ∀ x : ℝ, 2 ≤ x → x * ω x = 1 + ∫ t in (1 : ℝ)..(x - 1), ω t) :
    ∃ ε C : ℝ, 0 < ε ∧ ∀ n : ℕ, 1 ≤ n →
      |((∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ) ^ 2) /
            (n.factorial : ℝ) -
          ((∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ)) /
            (n.factorial : ℝ)) ^ 2) -
          n * (2 * ∫ x in Set.Ioi (1 : ℝ), ω x / x ^ 2)|
        ≤ C * (n : ℝ) * (n : ℝ) ^ (-ε)

/-- Theorem 3 (corrected): if `ω(n + (1+z)/2) = ∑_i c_{n,i} z^i` for `n ≥ 1` and
`-1 ≤ z < 1`, then `c_{1,i} = (2/3)(-1/3)^i`,
`c_{n+1,0} = (1/(2n+3)) ∑_i c_{n,i} (2(n+1) + (-1)^i/(i+1))` and
`c_{n+1,i} = (c_{n,i-1}/i - c_{n+1,i-1})/(2n+3)` for `n ≥ 1`, `i ≥ 1`. The
printed theorem has `c_{n,i}/n` in place of `c_{n,i-1}/i`; the paper's proof
derives `(2n+3) c_{n+1,i} + c_{n+1,i-1} = c_{n,i-1}/i`.

Source: Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab
Function and Revisiting the Variance of the Distribution of the Smallest
Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 3
(`integers-2024-A7-thm-3`). -/
public theorem_wanted buchstab_taylor_coeff_recursion (ω : ℝ → ℝ)
    (hω₁ : ∀ x ∈ Set.Icc (1 : ℝ) 2, ω x = 1 / x)
    (hω₂ : ∀ x : ℝ, 2 ≤ x → x * ω x = 1 + ∫ t in (1 : ℝ)..(x - 1), ω t)
    (c : ℕ → ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ Set.Ico (-1 : ℝ) 1,
      HasSum (fun i => c n i * z ^ i) (ω (n + (1 + z) / 2))) :
    (∀ i, c 1 i = 2 / 3 * (-1 / 3 : ℝ) ^ i) ∧
      (∀ n : ℕ, 1 ≤ n → c (n + 1) 0 =
        (∑' i, c n i * (2 * ((n : ℝ) + 1) + (-1 : ℝ) ^ i / ((i : ℝ) + 1))) /
          (2 * (n : ℝ) + 3)) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i : ℕ, 1 ≤ i →
        c (n + 1) i = (c n (i - 1) / i - c (n + 1) (i - 1)) / (2 * (n : ℝ) + 3))

/-- Theorem 4 (corrected at `c_{2,0}`): for `K > 0`, if
`Ω_K(n + (1+z)/2) = ∑_i c_{n,i} z^i` for `n ≥ 1` and `-1 ≤ z < 1`, then
`c_{1,0} = 1`, `c_{1,i} = 0` for `i ≥ 1`,
`c_{2,0} = 1 + K ∑_{i ≥ 1} (-1)^{i-1}/(i 2^i) = 1 + K log(3/2)`,
`c_{2,i} = K ∑_{j ≥ i} (-1)^{j-1} binom(j, i)/(j 2^j)` for `i ≥ 1`, and for `n ≥ 3`,
with `α_i = ∑_{j ≤ i} (-1)^{i-j} c_{n-1,j}/(2n-1)^{i-j}`,
`c_{n,0} = ∑_i c_{n-1,i} - (K/(2n-1)) ∑_i (-1)^{i+1} α_i/(i+1)` and
`c_{n,i} = K α_{i-1}/((2n-1) i)`. The printed `c_{2,0} = 1 + K ∑ 1/(i 2^i)`
omits the sign `(-1)^{i-1}`.

Source: Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab
Function and Revisiting the Variance of the Distribution of the Smallest
Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 4
(`integers-2024-A7-thm-4`). -/
public theorem_wanted generalized_buchstab_taylor_coeff_recursion (K : ℝ) (hK : 0 < K)
    (Ω : ℝ → ℝ) (hΩ₁ : ∀ x ∈ Set.Ico (1 : ℝ) 2, Ω x = 1)
    (hΩ₂ : ∀ x : ℝ, 2 ≤ x → Ω x = 1 + K * ∫ u in (2 : ℝ)..x, Ω (u - 1) / (u - 1))
    (c : ℕ → ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ Set.Ico (-1 : ℝ) 1,
      HasSum (fun i => c n i * z ^ i) (Ω (n + (1 + z) / 2))) :
    c 1 0 = 1 ∧ (∀ i : ℕ, 1 ≤ i → c 1 i = 0) ∧
      c 2 0 = 1 + K * ∑' i : ℕ, (-1 : ℝ) ^ i / (((i : ℝ) + 1) * 2 ^ (i + 1)) ∧
      (∀ i : ℕ, 1 ≤ i → c 2 i =
        K * ∑' j : ℕ, (-1 : ℝ) ^ (j + i - 1) * ((j + i).choose i : ℝ) /
          (((j : ℝ) + i) * 2 ^ (j + i))) ∧
      (∀ n : ℕ, 3 ≤ n → c n 0 = ∑' i, c (n - 1) i -
        K / (2 * (n : ℝ) - 1) * ∑' i : ℕ, (-1 : ℝ) ^ (i + 1) *
          (∑ j ∈ Finset.range (i + 1),
            (-1 : ℝ) ^ (i - j) / (2 * (n : ℝ) - 1) ^ (i - j) * c (n - 1) j) / ((i : ℝ) + 1)) ∧
      (∀ n : ℕ, 3 ≤ n → ∀ i : ℕ, 1 ≤ i → c n i =
        K * (∑ j ∈ Finset.range i,
            (-1 : ℝ) ^ (i - 1 - j) / (2 * (n : ℝ) - 1) ^ (i - 1 - j) * c (n - 1) j) /
          ((2 * (n : ℝ) - 1) * i))

end

end MetaMathlibExt
