/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

noncomputable section

namespace MathlibExt.Analysis.Fourier.SpectralConventions

/-!
# Spectral conventions for waves and the finite Fourier transform

Conventions for frequencies, wavenumbers, and the `1/N` normalization of the
discrete Fourier transform, plus finite structure factors and chain normal
modes. The DFT itself is Mathlib's `ZMod.dft`; no new DFT is defined.

## Conventions

* Exponent sign: `ZMod.dft Φ k = ∑ j, ZMod.stdAddChar (-(j * k)) • Φ j`
  (`ZMod.dft_apply`), i.e. the forward kernel is `exp (-2πi j k / N)`. This
  sign is Mathlib's and is not flipped here.
* Normalization: `ZMod.dft` is unnormalized and its inverse `ZMod.dft.symm`
  (Mathlib's scoped notation `𝓕⁻`, characterized by `ZMod.invDFT_apply`)
  carries the `1/N`. `normalizedDft` puts the `1/N` on the forward transform
  instead; `normalizedDft_eq_invDFT_neg` shows the two placements agree up to
  `k ↦ -k`.
* `2π`: the physics convention `ω = 2πν` and `k = 2π / λ` is used throughout.
  The crystallographic convention `k = 1 / λ` differs by `2π`; mixing the two
  produces a `2π` error.

## Model boundary and non-goals

Fourier identities are mathematics; plane-wave, scattering, and harmonic
assumptions are physical model inputs. `chainNormalModeFrequency` is the
textbook dispersion relation of a periodic monatomic chain (`N` masses `m`,
springs `K`), taken as a model input and not derived from dynamics. Only the
finite periodic case is treated: no continuous Fourier transform is claimed.
Reciprocal bases are not formalized here; they belong to the diffraction
modules.

## Clause map

* MF15.1: `dft_scaling`, `normalizedDft`, `normalizedDft_eq_invDFT_neg`.
* MF15.2: `angularFrequency`, `frequency`, `wavenumber`, `wavelength`, and the
  four round-trip lemmas.
* MF15.3: `structureFactor`, `structureFactor_eq_sum_amp_of_zero`,
  `structureFactor_twoSite_cancel`, `chainNormalModeFrequency`, and the
  `chainNormalModeFrequency_*` lemmas.

Reuse-verified exception: the roadmap prerequisites MF03 and MF04 are not
imported. This module depends only on pinned Mathlib (`ZMod.dft`,
`ZMod.stdAddChar`, real trigonometry) and on no MF03 or MF04 file.

Sources: atlas roadmap R09 and R11; task MF15, targets MF15.1–MF15.3.
-/

/-- Angular frequency `ω = 2πν` (physics convention). -/
def angularFrequency (ν : ℝ) : ℝ := 2 * Real.pi * ν

/-- Frequency `ν = ω / (2π)`. -/
def frequency (ω : ℝ) : ℝ := ω / (2 * Real.pi)

/-- Wavenumber `k = 2π / λ` (physics convention; NOT the crystallographic `1/λ`). -/
def wavenumber (lam : ℝ) : ℝ := 2 * Real.pi / lam

/-- Wavelength `λ = 2π / k`. -/
def wavelength (k : ℝ) : ℝ := 2 * Real.pi / k

/-- The `1/N`-normalized DFT: `ZMod.dft` with the `(N : ℂ)⁻¹` normalization. -/
noncomputable def normalizedDft {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) : ZMod N → ℂ :=
  fun k => (N : ℂ)⁻¹ * ZMod.dft Φ k

/-- Finite structure factor: amplitudes `amp i` at positions `pos i`, evaluated at
wavevector index `k`, with Mathlib's standard additive character. -/
noncomputable def structureFactor {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]
    (amp : ι → ℂ) (pos : ι → ZMod N) (k : ZMod N) : ℂ :=
  ∑ i, amp i * ZMod.stdAddChar (k * pos i)

/-- Textbook finite-chain normal-mode frequency (model input, not derived here):
`ω_j = 2 * sqrt(K / m) * |sin (π j / N)|`. -/
noncomputable def chainNormalModeFrequency (K m : ℝ) (N : ℕ) (j : ℕ) : ℝ :=
  2 * Real.sqrt (K / m) * |Real.sin (Real.pi * j / N)|

/-- Round-trip: `frequency (angularFrequency ν) = ν`. -/
theorem frequency_angularFrequency (ν : ℝ) :
    frequency (angularFrequency ν) = ν := by
  unfold frequency angularFrequency
  field_simp

/-- Round-trip: `angularFrequency (frequency ω) = ω`. -/
theorem angularFrequency_frequency (ω : ℝ) :
    angularFrequency (frequency ω) = ω := by
  unfold angularFrequency frequency
  field_simp

/-- Round-trip: `wavenumber (wavelength k) = k` for `k ≠ 0`. -/
theorem wavenumber_wavelength {k : ℝ} (hk : k ≠ 0) :
    wavenumber (wavelength k) = k := by
  unfold wavenumber wavelength
  field_simp

/-- Round-trip: `wavelength (wavenumber lam) = lam` for `lam ≠ 0`. -/
theorem wavelength_wavenumber {lam : ℝ} (hlam : lam ≠ 0) :
    wavelength (wavenumber lam) = lam := by
  unfold wavelength wavenumber
  field_simp

/-- Scaling a signal scales its DFT by the same constant (normalization invariance). -/
theorem dft_scaling {N : ℕ} [NeZero N] (c : ℂ) (Φ : ZMod N → ℂ) :
    ZMod.dft (c • Φ) = c • ZMod.dft Φ := by
  exact ZMod.dft_const_smul c Φ

/-- The `1/N`-normalized DFT is the inverse DFT at the negated frequency:
normalization and inversion are consistent. -/
theorem normalizedDft_eq_invDFT_neg {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (k : ZMod N) :
    normalizedDft Φ k = ZMod.dft.symm Φ (-k) := by
  simp only [normalizedDft, ZMod.invDFT_apply', neg_neg, smul_eq_mul]

/-- At zero wavevector the structure factor is the plain sum of amplitudes. -/
theorem structureFactor_eq_sum_amp_of_zero {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]
    (amp : ι → ℂ) (pos : ι → ZMod N) :
    structureFactor amp pos 0 = ∑ i, amp i := by
  simp only [structureFactor, zero_mul, AddChar.map_zero_eq_one, mul_one]

/-- Two-site motif cancellation: two equal amplitudes at positions `0` and `1` of
`ZMod 2`, evaluated at `k = 1`, interfere destructively to `0`. -/
theorem structureFactor_twoSite_cancel (a : ℂ) :
    structureFactor (fun _ : Fin 2 => a) ![0, 1] (1 : ZMod 2) = 0 := by
  have h1 : ZMod.stdAddChar (1 : ZMod 2) = -1 := by
    have h := ZMod.stdAddChar_coe (N := 2) 1
    rw [Int.cast_one] at h
    rw [h, ← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring
  simp [structureFactor, Fin.sum_univ_two, h1]

/-- The `j = 0` chain mode has frequency `0`. -/
theorem chainNormalModeFrequency_zero (K m : ℝ) (N : ℕ) :
    chainNormalModeFrequency K m N 0 = 0 := by
  simp only [chainNormalModeFrequency, Nat.cast_zero, mul_zero, zero_div,
    Real.sin_zero, abs_zero]

/-- Chain-mode frequencies are nonnegative when `K / m ≥ 0`. -/
theorem chainNormalModeFrequency_nonneg {K m : ℝ} (h : 0 ≤ K / m) (N : ℕ) (j : ℕ) :
    0 ≤ chainNormalModeFrequency K m N j := by
  -- Mathlib's `Real.sqrt` is nonnegative on all of `ℝ`, so `h` is not needed.
  unfold chainNormalModeFrequency
  positivity

/-- Chain-mode symmetry: mode `N - j` has the same frequency as mode `j`. -/
theorem chainNormalModeFrequency_symm {K m : ℝ} {N : ℕ} (hN : N ≠ 0) {j : ℕ} (hj : j ≤ N) :
    chainNormalModeFrequency K m N (N - j) = chainNormalModeFrequency K m N j := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have harg : Real.pi * ((N - j : ℕ) : ℝ) / N = Real.pi - Real.pi * j / N := by
    rw [Nat.cast_sub hj]
    field_simp
  simp only [chainNormalModeFrequency, harg, Real.sin_pi_sub]

end MathlibExt.Analysis.Fourier.SpectralConventions
