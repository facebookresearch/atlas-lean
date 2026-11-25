/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Chao's lower bound for the number of classes

A population has `S` classes. Under Poisson sampling, class `i` is observed a Poisson(`λᵢ`) number
of times, independently, with `λᵢ > 0`; let `f_k` be the number of classes observed exactly `k`
times and `S_obs = S - f₀` the number of classes observed. Then
`E[f_k] = ∑ᵢ e^{-λᵢ} λᵢᵏ / k!`, and the Cauchy–Schwarz inequality gives
`E[f₁]² ≤ E[f₀] · 2 E[f₂]`, i.e. `S ≥ E[S_obs] + E[f₁]² / (2 E[f₂])` (Chao 1984). This is why
`Chao1 = S_obs + f₁² / (2 f₂)` is a lower-bound estimator of `S`.

Recorded here: the exact inequality for the expected class frequencies under Poisson sampling.
The multinomial-sampling version, which holds only asymptotically, is not formalized. The primary
was not read locally; the inequality is derived from the Poisson model as stated, by
Cauchy–Schwarz.

Sources: A. Chao, "Nonparametric estimation of the number of classes in a population", Scand. J.
Statist. 11 (1984) 265–270.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.ChaoLowerBoundWanted

/-- The expected number `E[f_k] = ∑ᵢ e^{-λᵢ} λᵢᵏ / k!` of classes observed exactly `k` times
when class `i` is observed a Poisson(`λᵢ`) number of times. -/
noncomputable def expectedFreq {S : ℕ} (rate : Fin S → ℝ) (k : ℕ) : ℝ :=
  ∑ i, Real.exp (-rate i) * rate i ^ k / k.factorial

/-- **Chao's lower bound** (Chao 1984; derived for Poisson sampling): let there be `S` classes
with Poisson sampling rates `λᵢ > 0`, and suppose `E[f₂] > 0`. Then the number of classes is at
least the expected number observed plus `E[f₁]² / (2 E[f₂])`:
`E[S_obs] + E[f₁]² / (2 E[f₂]) ≤ S`, where `E[S_obs] = S - E[f₀]`.

Source: Chao (1984). -/
public theorem_wanted chao_lower_bound {S : ℕ} (rate : Fin S → ℝ) (hrate : ∀ i, 0 < rate i)
    (h₂ : 0 < expectedFreq rate 2) :
    ((S : ℝ) - expectedFreq rate 0) + expectedFreq rate 1 ^ 2 / (2 * expectedFreq rate 2) ≤ S

end WantedExt.Biology.StatisticalGenetics.ChaoLowerBoundWanted
