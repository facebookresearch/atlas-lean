/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.TorusSobolev.Basic

@[expose] public section

noncomputable section

namespace TorusSobolev

/-- Finite nonsingular parameters. The source's two limit endpoints are separate constructors. -/
abbrev FiniteExtremalParameter := {μ : ℝ // μ < -1 ∨ 0 < μ}

/-- The primary parameter domain `(-∞,-1] ∪ (0,∞]`, with its endpoints represented as limits. -/
inductive ExtremalParameter where
  | finite (μ : FiniteExtremalParameter)
  | firstShell
  | biharmonic

/-- Every reciprocal is used only under its nonzero-kernel qualification. -/
def KernelAdmissible : ExtremalParameter → Prop
  | .finite μ => ∀ k : Frequency, k ≠ 0 →
      frequencyWeight k ≠ 0 ∧ 1 + μ.1 * frequencyWeight k ≠ 0
  | .firstShell => True
  | .biharmonic => ∀ k : Frequency, k ≠ 0 → frequencyWeight k ≠ 0

/-- The primary coefficients of the unscaled conditional family. -/
def extremalCoefficient (p : ExtremalParameter) (_hp : KernelAdmissible p) (k : Frequency) : ℂ :=
  match p with
  | .finite μ => if k = 0 then 0 else
      ((2 * Real.pi / (frequencyWeight k * (1 + μ.1 * frequencyWeight k)) : ℝ) : ℂ)
  | .firstShell => if frequencyWeight k = 1 then (Real.pi : ℂ) else 0
  | .biharmonic => if k = 0 then 0 else ((2 * Real.pi / frequencyWeight k ^ 2 : ℝ) : ℂ)

/-- The actual Fourier family, including convergent infinite evaluation and normalization. -/
def IsExplicitExtremal (u : C(Torus, ℝ)) : Prop :=
  ∃ p : ExtremalParameter, ∃ hp : KernelAdmissible p, ∃ a : ℝ,
    a ≠ 0 ∧ Summable (extremalCoefficient p hp) ∧
      (∀ k : Frequency, fourierCoefficient u k = (a : ℂ) * extremalCoefficient p hp k) ∧
      ∀ x : Torus, (u x : ℂ) = (2 * Real.pi : ℂ)⁻¹ *
        ∑' k : Frequency, (a : ℂ) * extremalCoefficient p hp k *
          UnitAddTorus.mFourier k (unitRescaling x)

/-- Translation and nonzero real scaling describe the source's extremal orbit. -/
def SameExtremalOrbit (u v : C(Torus, ℝ)) : Prop :=
  ∃ a : ℝ, a ≠ 0 ∧ ∃ x₀ : Torus, ∀ x : Torus, v x = a * u (x - x₀)

end TorusSobolev
