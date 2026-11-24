/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.BuchstabTaylor
public import MathlibExt.Combinatorics.Enumerative.GeneralizedBuchstabTaylor
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

/-- **Mean length of the smallest cycle of a random permutation.** For $n \ge 1$ let $X_n$ be the
length of the smallest cycle of a uniformly random permutation of $\{1, \dots, n\}$. Then
$\mathbb{E}(X_n) / (e^{-\gamma} \log n) \to 1$ as $n \to \infty$, where $\gamma$ is the
Euler–Mascheroni constant.

The paper states this as $\mathbb{E}(X_n) = e^{-\gamma} \log n \, (1 + O(h(n)/\log n))$ for some
$h(n) = o(\log n)$, which is equivalent.

Source: Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab
Function and Revisiting the Variance of the Distribution of the Smallest
Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 1
(`integers-2024-A7-thm-1`). -/
public theorem_wanted smallest_cycle_mean_asymp :
    Filter.Tendsto (fun n : ℕ =>
      ((∑ σ : Equiv.Perm (Fin n), ((⨅ x, Function.minimalPeriod σ x : ℕ) : ℝ)) /
          (n.factorial : ℝ)) / (Real.exp (-eulerMascheroniConstant) * Real.log n))
      Filter.atTop (nhds 1)

/-- **Higher moments of the smallest cycle length.** Let $\omega$ be a real function with
$\omega(x) = 1/x$ for $1 \le x \le 2$ and $x\,\omega(x) = 1 + \int_1^{x-1} \omega(t)\,dt$ for
$x \ge 2$, and for $n \ge 1$ let $X_n$ be the length of the smallest cycle of a uniformly random
permutation of $\{1, \dots, n\}$. For every integer $\ell \ge 2$ there are real constants
$\varepsilon > 0$ and $C$ such that for every $n \ge 1$

$$\left| \mathbb{E}(X_n^\ell) - \ell\, n^{\ell-1} \int_1^\infty \frac{\omega(x)}{x^\ell}\,dx \right|
\le C\, n^{\ell-1} n^{-\varepsilon}.$$

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

/-- **Variance of the smallest cycle length.** Let $\omega$ be a real function with
$\omega(x) = 1/x$ for $1 \le x \le 2$ and $x\,\omega(x) = 1 + \int_1^{x-1} \omega(t)\,dt$ for
$x \ge 2$, and for $n \ge 1$ let $X_n$ be the length of the smallest cycle of a uniformly random
permutation of $\{1, \dots, n\}$. There are real constants $\varepsilon > 0$ and $C$ such that for
every $n \ge 1$

$$\left| \operatorname{Var}(X_n) - 2n \int_1^\infty \frac{\omega(x)}{x^2}\,dx \right|
\le C\, n \cdot n^{-\varepsilon}.$$

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

end

end MetaMathlibExt
