/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Wavelet.Scattering1D

/-!
# Tests for the one-dimensional scattering definitions
-/

open MeasureTheory
open MathlibExt.Analysis.Wavelet.Scattering1D MathlibExt.Analysis.Wavelet.ScatteringCascade

namespace MathlibExtTest.Analysis.Wavelet.Scattering1D

/-- At `j = 0` the dilated wavelet is the wavelet itself. -/
example (ψ : ℝ → ℂ) : dilate ψ 0 = ψ := by
  funext x; simp [dilate]

/-- At `J = 0` the low-pass window is `φ` itself. -/
example (φ : ℝ → ℂ) : lowPass φ 0 = φ := by
  funext x; simp [lowPass]

/-- On the empty path the windowed scattering is the low-pass average `A_J f = f ⋆ φ_{2^J}`. -/
example (ψ φ f : ℝ → ℂ) (J : ℤ) (p : Fin 0 → {j : ℤ // -J < j}) :
    windowedScattering ψ φ J p f =
      convolution f (lowPass φ J) (ContinuousLinearMap.lsmul ℂ ℂ) volume := by
  simp [windowedScattering]

/-- The modulus layer takes real nonnegative values. -/
example (ψ h : ℝ → ℂ) (j : ℤ) (x : ℝ) :
    (modulusLayer ψ j h x).im = 0 ∧ 0 ≤ (modulusLayer ψ j h x).re := by
  simp [modulusLayer]

end MathlibExtTest.Analysis.Wavelet.Scattering1D
