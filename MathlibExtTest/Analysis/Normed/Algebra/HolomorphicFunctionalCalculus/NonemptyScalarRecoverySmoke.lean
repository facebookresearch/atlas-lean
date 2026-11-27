/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic

/-!
# Nonempty scalar recovery by the Riesz functional calculus

In the complete complex normed algebra `ℂ`, the spectrum of `i` is the singleton `{i}`.
The coordinate germ constructs an admissible grid contour with index one at `i`. The actual
normalized Riesz integral over that contour recovers the nonzero scalar `i`, and the Riesz
functional calculus sends the sum of the constant-one and coordinate germs to `1 + i`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace NonemptyScalarRecoverySmoke

private def coordinate : HolomorphicNearSpectrum (Complex.I : ℂ) :=
  HolomorphicNearSpectrum.coordinate (Complex.I : ℂ)

private def contour : GridFilling :=
  HolomorphicNearSpectrum.contour (Complex.I : ℂ) coordinate

private theorem scalar_spectrum : spectrum ℂ (Complex.I : ℂ) = {Complex.I} :=
  spectrum.scalar_eq (𝕜 := ℂ) (A := ℂ) Complex.I

private theorem scalar_mem_spectrum : Complex.I ∈ spectrum ℂ (Complex.I : ℂ) := by
  rw [scalar_spectrum]
  rfl

private theorem contour_admissible :
    contour.IsAdmissibleFor (spectrum ℂ (Complex.I : ℂ))
      (HolomorphicNearSpectrum.analyticDomain (Complex.I : ℂ) coordinate) :=
  HolomorphicNearSpectrum.contour_isAdmissibleFor (Complex.I : ℂ) coordinate

private theorem coordinate_recovery :
    rieszFunctionalCalculus (Complex.I : ℂ) coordinate = Complex.I :=
  rieszFunctionalCalculus_coordinate (Complex.I : ℂ)

private theorem contour_recovery :
    rieszIntegral contour.toCycle (Complex.I : ℂ)
      (HolomorphicNearSpectrum.rep (Complex.I : ℂ) coordinate) = Complex.I := by
  have h := rieszFunctionalCalculus_eq_rieszIntegral_rep
    (Complex.I : ℂ) coordinate contour contour_admissible
  exact h.symm.trans coordinate_recovery

example : spectrum ℂ (Complex.I : ℂ) = {Complex.I} ∧
    contour.toCycle.index Complex.I = 1 ∧ (Complex.I : ℂ) ≠ 0 := by
  exact ⟨scalar_spectrum, contour_admissible.2.1 Complex.I scalar_mem_spectrum,
    Complex.I_ne_zero⟩

example : rieszIntegral contour.toCycle (Complex.I : ℂ)
      (HolomorphicNearSpectrum.rep (Complex.I : ℂ) coordinate) = Complex.I ∧
    rieszFunctionalCalculus (Complex.I : ℂ) coordinate = Complex.I :=
  ⟨contour_recovery, coordinate_recovery⟩

example :
    rieszFunctionalCalculus (Complex.I : ℂ)
      ((1 : HolomorphicNearSpectrum (Complex.I : ℂ)) + coordinate) = 1 + Complex.I := by
  rw [rieszFunctionalCalculus_add, rieszFunctionalCalculus_one, coordinate_recovery]

end NonemptyScalarRecoverySmoke
