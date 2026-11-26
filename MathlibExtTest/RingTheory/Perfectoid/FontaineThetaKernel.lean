/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.Perfectoid.FontaineThetaKernel

/-! Tests for the kernel of Fontaine's map `θ` for `𝓞_ℂ_[p]`: `ξ = p - [p♭]` is a nonzero element
of the kernel, it generates the kernel before and after inverting `p`, every unit multiple of `ξ`
generates the kernel too, and the tilt is a domain. -/

open Ideal WittVector

variable (p : ℕ) [Fact p.Prime]

example : IsDomain (PreTilt 𝓞_ℂ_[p] p) := inferInstance

example : (PadicComplexInt.pFlat p).untilt = p := PadicComplexInt.untilt_pFlat p

example : fontaineTheta 𝓞_ℂ_[p] p (PadicComplexInt.xi p) = 0 := PadicComplexInt.fontaineTheta_xi p

example : PadicComplexInt.xi p ≠ 0 := PadicComplexInt.xi_ne_zero p

-- `-ξ`, a unit multiple of `ξ`, generates the same kernel.
example : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {(-PadicComplexInt.xi p)} := by
  rw [PadicComplexInt.ker_fontaineTheta_eq_span_xi, ← Ideal.span_singleton_neg]

example (m : ℕ) :
    RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p) ^ m =
      span {(algebraMap _ (Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)))
        (PadicComplexInt.xi p) ^ m)} :=
  PadicComplexInt.ker_fontaineThetaInvertP_pow_eq_span_xi_pow p m

-- The generic criterion, applied to `θ` and `ξ` directly.
example : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) =
    span {(p : WittVector p (PreTilt 𝓞_ℂ_[p] p)) - teichmuller p (PadicComplexInt.pFlat p)} :=
  WittVector.ker_fontaineTheta_eq_span
    (fun _ hb => (mul_eq_zero.mp hb).resolve_left
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
    (PadicComplexInt.pFlat p) (PadicComplexInt.untilt_pFlat p)
    (PadicComplexInt.dvd_of_coeff_zero_eq_zero p _ (PadicComplexInt.untilt_pFlat p))
