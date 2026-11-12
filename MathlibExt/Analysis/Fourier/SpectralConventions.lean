/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.ZMod

@[expose] public section

noncomputable section

namespace MathlibExt.Analysis.Fourier.SpectralConventions

/-!
# Spectral conventions for the finite Fourier transform

The `1/N` normalization of the discrete Fourier transform. The DFT itself is
Mathlib's `ZMod.dft`; no new DFT is defined.

## Conventions

* Exponent sign: `ZMod.dft Φ k = ∑ j, ZMod.stdAddChar (-(j * k)) • Φ j`
  (`ZMod.dft_apply`), i.e. the forward kernel is `exp (-2πi j k / N)`. This
  sign is Mathlib's and is not flipped here.
* Normalization: `ZMod.dft` is unnormalized and its inverse `ZMod.dft.symm`
  (Mathlib's scoped notation `𝓕⁻`, characterized by `ZMod.invDFT_apply`)
  carries the `1/N`. `normalizedDft` puts the `1/N` on the forward transform
  instead; `normalizedDft_eq_invDFT_neg` shows the two placements agree up to
  `k ↦ -k`.

Physical wave, structure-factor, and chain-mode conventions (angular
frequency, wavenumber, `structureFactor`, `chainNormalModeFrequency`) live in
`PhyslibExt.Analysis.Fourier.SpectralConventions`, not here: they are physics
model inputs, not generic Fourier mathematics.

## Clause map

* MF15.1: `normalizedDft`, `normalizedDft_eq_invDFT_neg`.

Reuse-verified exception: the roadmap prerequisites MF03 and MF04 are not
imported. This module depends only on pinned Mathlib (`ZMod.dft`,
`ZMod.stdAddChar`) and on no MF03 or MF04 file.

Sources: atlas roadmap R09 and R11; task MF15, target MF15.1.
-/

/-- The `1/N`-normalized DFT: `ZMod.dft` with the `(N : ℂ)⁻¹` normalization. -/
noncomputable def normalizedDft {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) : ZMod N → ℂ :=
  fun k => (N : ℂ)⁻¹ * ZMod.dft Φ k

/-- The `1/N`-normalized DFT is the inverse DFT at the negated frequency:
normalization and inversion are consistent. -/
theorem normalizedDft_eq_invDFT_neg {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (k : ZMod N) :
    normalizedDft Φ k = ZMod.dft.symm Φ (-k) := by
  simp only [normalizedDft, ZMod.invDFT_apply', neg_neg, smul_eq_mul]

end MathlibExt.Analysis.Fourier.SpectralConventions
