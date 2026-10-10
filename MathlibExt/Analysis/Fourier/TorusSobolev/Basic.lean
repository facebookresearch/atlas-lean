/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Data.EReal.Operations

/-!
# Fourier Sobolev optimization on the two-dimensional torus

Actual real continuous functions on the period-`2π` torus, their canonical Haar
Fourier coefficients, full spectral `H²`, and global logarithmic optimization.
The supremum definitions do not assume finiteness or attainment. Equivalence to
physical weak-derivative energies is a separate mathematical bridge.
-/

@[expose] public section

noncomputable section

namespace TorusSobolev

/-- The actual torus with period `2*pi` in each coordinate. -/
abbrev Torus := Fin 2 → AddCircle (2 * Real.pi)

/-- The source integer-frequency lattice. -/
abbrev Frequency := Fin 2 → ℤ

/-- Canonical coordinate rescaling from physical period `2*pi` to unit period. -/
def unitRescaling : Torus ≃ₜ UnitAddTorus (Fin 2) :=
  Homeomorph.piCongrRight fun _ ↦
    AddCircle.homeomorphAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero

/-- The actual real function, expressed on the unit torus for normalized Haar Fourier analysis. -/
def unitRepresentative (u : C(Torus, ℝ)) : C(UnitAddTorus (Fin 2), ℂ) where
  toFun x := (u (unitRescaling.symm x) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (u.continuous.comp unitRescaling.symm.continuous)

/-- Primary coefficients: `a_k = 2π c_k`, where `c_k` uses normalized Haar measure. -/
def fourierCoefficient (u : C(Torus, ℝ)) (k : Frequency) : ℂ :=
  (2 * Real.pi : ℂ) * UnitAddTorus.mFourierCoeff (unitRepresentative u) k

/-- The squared physical frequency, for a torus of period `2π`. -/
def frequencyWeight (k : Frequency) : ℝ := ∑ i, (k i : ℝ) ^ 2

/-- Parseval gradient energy with the primary's real-Lebesgue normalization. -/
def gradientEnergy (u : C(Torus, ℝ)) : ℝ :=
  ∑' k, frequencyWeight k * ‖fourierCoefficient u k‖ ^ 2

/-- Parseval Laplacian energy with the primary's real-Lebesgue normalization. -/
def laplaceEnergy (u : C(Torus, ℝ)) : ℝ :=
  ∑' k, frequencyWeight k ^ 2 * ‖fourierCoefficient u k‖ ^ 2

/-- Full spectral `H²`, not merely finite Fourier polynomials. -/
def IsH2 (u : C(Torus, ℝ)) : Prop :=
  Summable fun k ↦ (1 + frequencyWeight k) ^ 2 * ‖fourierCoefficient u k‖ ^ 2

/-- Normalized product Haar measure, used explicitly for the actual mean. -/
def unitHaar : MeasureTheory.Measure (UnitAddTorus (Fin 2)) :=
  MeasureTheory.Measure.pi fun _ : Fin 2 ↦ AddCircle.haarAddCircle

/-- The integral of the actual real function; physical mean is `(2π)²` times this mean. -/
def mean (u : C(Torus, ℝ)) : ℝ :=
  ∫ y, u (unitRescaling.symm y) ∂unitHaar

/-- Actual zero-mean real `H²` functions on the period-`2π` torus. -/
def IsZeroMeanH2 (u : C(Torus, ℝ)) : Prop := IsH2 u ∧ mean u = 0

/-- The source's conditional variational constraints on actual functions. -/
def ConditionalAdmissible (u : C(Torus, ℝ)) (δ : ℝ) : Prop :=
  IsZeroMeanH2 u ∧ gradientEnergy u = 1 ∧ laplaceEnergy u = δ

/-- Actual point values of admissible functions, embedded in the extended reals. -/
def conditionalPointValues (δ : ℝ) : Set EReal :=
  (fun u : C(Torus, ℝ) ↦ (((u 0) ^ 2 : ℝ) : EReal)) '' {u | ConditionalAdmissible u δ}

/-- The conditional supremum, without an implicit finiteness assumption. -/
def theta (δ : ℝ) : EReal := sSup (conditionalPointValues δ)

/-- The source's frequency ratio; applications require positive gradient energy. -/
def frequencyRatio (u : C(Torus, ℝ)) : ℝ := laplaceEnergy u / gradientEnergy u

/-- The global additive remainder expression from the primary. -/
def remainder (δ : ℝ) : EReal :=
  ((4 * Real.pi : ℝ) : EReal) * theta δ - (Real.log δ : EReal) -
    (Real.log (1 + Real.log δ) : EReal)

/-- The primary takes all `δ ≥ 1`, not merely sufficiently large ratios. -/
def sharpRemainderValues : Set EReal := remainder '' Set.Ici 1

/-- The actual sharp global remainder, with finite attainment recorded separately. -/
def sharpRemainderValue : EReal := sSup sharpRemainderValues

/-- The primary inequality, quantified over actual functions and every point of the torus. -/
def UniformRemainderBound (L : ℝ) : Prop :=
  ∀ u : C(Torus, ℝ), IsZeroMeanH2 u → 0 < gradientEnergy u → 1 ≤ frequencyRatio u →
    ∀ x : Torus, (u x) ^ 2 ≤ gradientEnergy u / (4 * Real.pi) *
      (Real.log (frequencyRatio u) + Real.log (1 + Real.log (frequencyRatio u)) + L)

end TorusSobolev
