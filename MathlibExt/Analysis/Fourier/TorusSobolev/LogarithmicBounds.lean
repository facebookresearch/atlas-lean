/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.TorusSobolev.Basic

/-!
# One-log and double-log bounds on actual torus functions

The coefficients quantify uniformly over the full zero-mean spectral `H²` class.
The ratio guards exclude zero gradient energy and keep the logarithms in their
source domain. These definitions assert no sharpness or existence theorem.
-/

@[expose] public section

noncomputable section

namespace TorusSobolev

/-- The one-log inequality, including a finite additive constant. -/
def OneLogBound (c K : ℝ) : Prop :=
  ∀ u : C(Torus, ℝ), IsZeroMeanH2 u → 0 < gradientEnergy u → 1 ≤ frequencyRatio u →
    ∀ x : Torus, (u x) ^ 2 ≤ c * gradientEnergy u * (Real.log (frequencyRatio u) + K)

/-- The double-log coefficient with the endpoint-safe `1 + log δ`. -/
def DoubleLogBound (a L : ℝ) : Prop :=
  ∀ u : C(Torus, ℝ), IsZeroMeanH2 u → 0 < gradientEnergy u → 1 ≤ frequencyRatio u →
    ∀ x : Torus, (u x) ^ 2 ≤ gradientEnergy u / (4 * Real.pi) *
      (Real.log (frequencyRatio u) + a * Real.log (1 + Real.log (frequencyRatio u)) + L)

/-- The infimum over leading coefficients whose actual uniform bound holds. -/
def oneLogLeadingCoefficientInfimum : EReal :=
  sInf ((fun c : ℝ ↦ (c : EReal)) '' {c | ∃ K : ℝ, OneLogBound c K})

end TorusSobolev
