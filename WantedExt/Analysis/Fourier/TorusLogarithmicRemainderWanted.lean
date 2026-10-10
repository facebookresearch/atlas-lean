/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.TorusSobolev.Fourier
public import MathlibExt.Analysis.Fourier.TorusSobolev.Extremals
public import MathlibExt.Analysis.Fourier.TorusSobolev.LogarithmicBounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Batteries.Util.ProofWanted

/-!
# Known logarithmic-remainder results awaiting proofs

Source: Bartuccelli, Deane and Zelik, arXiv:1012.2061v1, raw draft 30.09.10.
These fourteen private `ProofWanted` values are data, not proofs or open conjectures.
All constants and functions in their claims are actual upstream torus definitions.
The numerical value, maximizing ratio, global uniqueness, and Theta0 envelope are
nonasserting context. The full source allocation is in
`WantedExt/Sources/TorusLogarithmicRemainder.md`.
-/

@[expose] public section

noncomputable section

namespace TorusSobolev.LogarithmicRemainderWanted

open TorusSobolev

/-- Exact beta from the primary's Appendix, expressed without a decimal surrogate.
Source: arXiv:1012.2061v1, Appendix constant formula, lines 1901-1915.
-/
def beta : ℝ :=
  Real.pi * (2 * Real.eulerMascheroniConstant + 2 * Real.log 2 + 3 * Real.log Real.pi -
    4 * Real.log (Real.Gamma (1 / 4)))

/-- Conjugate symmetry for the actual real-function coefficients.
Source: arXiv:1012.2061v1, Fourier convention (1.f), lines 349-360; realness bridge.
-/
private theorem_wanted fourierCoefficient_conjugate (u : C(Torus, ℝ)) (k : Frequency) :
  fourierCoefficient u (-k) = star (fourierCoefficient u k)

/-- Absolute Fourier summability of the full spectral H2 class.
Source: arXiv:1012.2061v1, (1.theta) and (1.f), lines 327-360; canonical Sobolev bridge.
-/
private theorem_wanted h2AbsoluteFourierSummability (u : C(Torus, ℝ)) (h : IsH2 u) :
  Summable (UnitAddTorus.mFourierCoeff (unitRepresentative u))

/-- Nonsingularity of every qualified kernel, including the separate limits.
Source: arXiv:1012.2061v1, conditional family and endpoints, lines 410-465.
-/
private theorem_wanted extremalKernelAdmissibility (p : ExtremalParameter) : KernelAdmissible p

/-- Conditional attainment on the actual feasible domain delta >= 1.
Source: arXiv:1012.2061v1, Lemma Lem1.exist, lines 362-364.
-/
private theorem_wanted conditionalAttainment (δ : ℝ) (hδ : 1 ≤ δ) :
  ∃ u : C(Torus, ℝ), ConditionalAdmissible u δ ∧ (((u 0) ^ 2 : ℝ) : EReal) = theta δ

/-- The conditional optimizer has the qualified Fourier-kernel form.
Source: arXiv:1012.2061v1, Theorem Th1.ext, lines 410-435.
The printed delta > 0 is restricted to the feasible delta >= 1 domain.
-/
private theorem_wanted explicitConditionalExtremal (δ : ℝ) (hδ : 1 ≤ δ) :
  ∃ u : C(Torus, ℝ), ConditionalAdmissible u δ ∧
    (((u 0) ^ 2 : ℝ) : EReal) = theta δ ∧ IsExplicitExtremal u

/-- Conditional, not global, uniqueness up to translation and real scaling.
Source: arXiv:1012.2061v1, Theorem Th1.ext, lines 410-435.
-/
private theorem_wanted conditionalUniqueOrbit (δ : ℝ) (hδ : 1 ≤ δ) (u v : C(Torus, ℝ))
    (hu : ConditionalAdmissible u δ) (hv : ConditionalAdmissible v δ)
    (huMax : (((u 0) ^ 2 : ℝ) : EReal) = theta δ)
    (hvMax : (((v 0) ^ 2 : ℝ) : EReal) = theta δ) : SameExtremalOrbit u v

/-- The actual global optimal remainder is a finite real number.
Source: arXiv:1012.2061v1, Theorem Th2.loglog, lines 739-762.
-/
private theorem_wanted sharpRemainderFinite : ∃ L : ℝ, sharpRemainderValue = (L : EReal)

/-- The rigorous strict asymptotic-constant lower bound for the global remainder.
Source: arXiv:1012.2061v1, (2.const), lines 739-762; exact beta in the Appendix.
-/
private theorem_wanted strictBetaLowerBound :
  (((beta + Real.pi) / Real.pi : ℝ) : EReal) < sharpRemainderValue

/-- A ratio strictly larger than one attains the actual global remainder.
Source: arXiv:1012.2061v1, proof of Theorem Th2.loglog, lines 748-762.
-/
private theorem_wanted finiteGlobalAttainment :
  ∃ δ : ℝ, 1 < δ ∧ remainder δ = sharpRemainderValue

/-- Equivalence of the all-point uniform inequality and the global supremum bound.
Source: arXiv:1012.2061v1, (2.in-loglog) and (2.const), lines 739-748;
normalization and translation bridge for the actual full spectral model.
-/
private theorem_wanted sharpUniformCharacterization (L : ℝ) :
  UniformRemainderBound L ↔ sharpRemainderValue ≤ (L : EReal)

/-- A shared finite constant, ratio, and actual function witness sharp equality.
Source: arXiv:1012.2061v1, Theorem Th2.loglog, lines 739-762.
No numerical value or globally unique maximizing ratio is asserted.
-/
private theorem_wanted exactGlobalExtremal :
  ∃ L δ : ℝ, ∃ u : C(Torus, ℝ), sharpRemainderValue = (L : EReal) ∧
    UniformRemainderBound L ∧ 1 < δ ∧ ConditionalAdmissible u δ ∧
    (((u 0) ^ 2 : ℝ) : EReal) = theta δ ∧ IsExplicitExtremal u ∧
    (u 0) ^ 2 = 1 / (4 * Real.pi) * (Real.log δ + Real.log (1 + Real.log δ) + L)

/-- The infimum of actual one-log leading coefficients is exactly 1/(4*pi).
Source: Optimization Problems constants/16a.md, line 42; arXiv:1012.2061v1,
asymptotic formula (2.loglog), lines 692-703, and Theorem Th2.loglog, lines 739-762.
-/
private theorem_wanted oneLogLeadingInfimum :
  oneLogLeadingCoefficientInfimum = ((1 / (4 * Real.pi) : ℝ) : EReal)

/-- The sharp one-log leading coefficient admits no finite additive constant.
Source: Optimization Problems constants/16a.md, line 42; arXiv:1012.2061v1,
asymptotic formula (2.loglog), lines 692-703.
-/
private theorem_wanted oneLogSharpCoefficientNotAttained :
  ¬ ∃ K : ℝ, OneLogBound (1 / (4 * Real.pi)) K

/-- Any strictly smaller double-log coefficient admits no finite uniform remainder.
Source: arXiv:1012.2061v1, (2.loglog), lines 692-703;
Optimization Problems constants/16a.md, line 41, double-log sharpness clause.
-/
private theorem_wanted doubleLogNecessary (a : ℝ) (ha : a < 1) : ¬ ∃ L : ℝ, DoubleLogBound a L

end TorusSobolev.LogarithmicRemainderWanted
