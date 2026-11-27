/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Finite AM modulation and its DFT sidebands

## i. Overview

Amplitude modulation in the finite Fourier model on `ZMod N`: the
signal `(A + μ mⱼ) cos(2πkj/N)` (additive modulation coefficient
`μ`; the roadmap contract's model, not the dimensionless index of
`A(1 + μ m)`) has a discrete Fourier transform given by the
carrier impulses plus the message spectrum shifted to `k` and
`-k`. Each shifted copy is the full spectral replica centered at
`±k`; for a tone message it contains both conventional sidebands
`k ± f`. When the two shifted supports are disjoint, the
transform on each support, away from the carrier bins `k` and
`-k` themselves, is exactly the corresponding shifted message
spectrum; at the carrier bins the carrier impulse `A N / 2` is
also present, which is why the reading lemmas exclude them.
Constant and tone messages are worked out, and the
`N = 4` tone case shows the shifted supports need not be
disjoint.

## ii. Key results

- `dft_amSignal`: the DFT of the AM signal in terms of the
  message spectrum.
- `dft_amSignal_eq_positive_shift` and
  `dft_amSignal_eq_negative_shift`: the shifted-replica readings
  under disjointness, at bins other than the carrier bins.
- `dft_amSignal_const_message` and `dft_amSignal_tone_message`:
  the constant and tone validations.

## iii. Table of contents

- A. The finite AM model and its spectrum

## iv. References

- B. P. Lathi and Z. Ding, *Modern Digital and Analog Communication
Systems*, fifth edition, Oxford University Press, 2019: amplitude modulation and its spectrum.

## A. The finite AM model and its spectrum
-/

@[expose] public section

namespace PhyslibExt.Communications.FiniteAMModulator

open ZMod

/-- The sampled carrier `cos(2π k j / N)` on `ZMod N`, via `ZMod.val` lifts. -/
noncomputable def carrierCos (N : ℕ) [NeZero N] (k j : ZMod N) : ℝ :=
  Real.cos (2 * Real.pi * (k.val : ℝ) * (j.val : ℝ) / (N : ℝ))

/-- The finite AM signal `s_j = (A + μ m_j) cos(2π k j / N)`. -/
noncomputable def amSignal (N : ℕ) [NeZero N] (A μ : ℝ) (m : ZMod N → ℝ) (k : ZMod N) :
    ZMod N → ℝ :=
  fun j => (A + μ * m j) * carrierCos N k j

/-- The canonical (Mathlib, negative-exponent, unnormalized) DFT of a real message. -/
noncomputable def messageSpectrum (N : ℕ) [NeZero N] (m : ZMod N → ℝ) : ZMod N → ℂ :=
  𝓕 (fun j => (m j : ℂ))

/-- Bins carrying the positively shifted replica `M (l - k)`: the
full copy of the message spectrum centered at `k`, containing
both conventional sidebands `k ± f` for a tone at `f`. -/
noncomputable def positiveShiftSupport (N : ℕ) [NeZero N] (m : ZMod N → ℝ)
    (k : ZMod N) : Set (ZMod N) :=
  Function.support (fun l => messageSpectrum N m (l - k))

/-- Bins carrying the negatively shifted replica `M (l + k)`: the
full copy of the message spectrum centered at `-k`, containing
both conventional sidebands `-k ± f` for a tone at `f`. -/
noncomputable def negativeShiftSupport (N : ℕ) [NeZero N] (m : ZMod N → ℝ)
    (k : ZMod N) : Set (ZMod N) :=
  Function.support (fun l => messageSpectrum N m (l + k))

/-- The sampled carrier is the average of two conjugate characters. -/
lemma carrierCos_eq_stdAddChar (N : ℕ) [NeZero N] (k j : ZMod N) :
    ((carrierCos N k j : ℝ) : ℂ) = (stdAddChar (k * j) + stdAddChar (-(k * j))) / 2 := by
  have hkj : k * j = ((((k.val * j.val : ℕ) : ℤ)) : ZMod N) := by
    have e1 : ((k.val : ℕ) : ZMod N) = k := ZMod.natCast_zmod_val k
    have e2 : ((j.val : ℕ) : ZMod N) = j := ZMod.natCast_zmod_val j
    calc k * j = ((k.val : ℕ) : ZMod N) * ((j.val : ℕ) : ZMod N) := by rw [e1, e2]
    _ = ((((k.val * j.val : ℕ) : ℤ)) : ZMod N) := by push_cast; ring
  have e1 : stdAddChar (k * j)
      = Complex.exp (((((2 * Real.pi * k.val * j.val / N : ℝ)) : ℂ)) * Complex.I) := by
    rw [hkj, stdAddChar_coe]
    congr 1
    push_cast
    ring
  have e2 : stdAddChar (-(k * j))
      = Complex.exp ((-((((2 * Real.pi * k.val * j.val / N : ℝ)) : ℂ))) * Complex.I) := by
    rw [hkj, ← Int.cast_neg, stdAddChar_coe]
    congr 1
    push_cast
    ring
  unfold carrierCos
  rw [e1, e2, Complex.ofReal_cos]
  have h2 := Complex.two_cos (((2 * Real.pi * k.val * j.val / N : ℝ)) : ℂ)
  rw [← h2]
  ring

/-- Modulation shift: multiplying by the character `j ↦ e^{2πi k j / N}` shifts the
canonical DFT by `k`. -/
lemma dft_stdAddChar_mul (N : ℕ) [NeZero N] (Φ : ZMod N → ℂ) (k l : ZMod N) :
    𝓕 (fun j => stdAddChar (k * j) * Φ j) l = 𝓕 Φ (l - k) := by
  simp only [dft_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 1
  congr 1
  ring

/-- A pure complex tone at bin `k` has DFT `N` times the impulse at `k`. -/
lemma dft_stdAddChar (N : ℕ) [NeZero N] (k l : ZMod N) :
    𝓕 (fun j => stdAddChar (k * j)) l = (N : ℂ) * (Pi.single k (1 : ℂ) : ZMod N → ℂ) l := by
  simp only [dft_apply, smul_eq_mul]
  have hsum : ∀ j : ZMod N,
      stdAddChar (-(j * l)) * stdAddChar (k * j) = stdAddChar ((k - l) * j) := by
    intro j
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [hsum]
  by_cases h : k - l = 0
  · have hlk : l = k := (sub_eq_zero.mp h).symm
    simp only [h, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one]
    rw [hlk, Pi.single_eq_same]
    ring
  · have hlk : l ≠ k := fun heq => h (by rw [heq, sub_self])
    have hzero : ∑ j : ZMod N, stdAddChar ((k - l) * j) = 0 :=
      AddChar.sum_eq_zero_of_ne_one ((isPrimitive_stdAddChar N) h)
    rw [hzero]
    simp [Pi.single_apply, hlk]

/-- **Finite AM spectrum.** The canonical DFT of `s_j = (A + μ m_j) cos(2π k j / N)` is
`A N / 2` times the impulses at `k` and `-k` plus `μ / 2` times the two shifted
transforms of `m`. No support hypothesis: coinciding bins add. -/
lemma dft_amSignal (N : ℕ) [NeZero N] (A μ : ℝ) (m : ZMod N → ℝ) (k l : ZMod N) :
    𝓕 (fun j => ((amSignal N A μ m k j : ℝ) : ℂ)) l =
      (A : ℂ) * (N : ℂ) / 2 * ((Pi.single k (1 : ℂ) : ZMod N → ℂ) l + (Pi.single (-k) (1 : ℂ) : ZMod N → ℂ) l) +
        (μ : ℂ) / 2 * (messageSpectrum N m (l - k) + messageSpectrum N m (l + k)) := by
  have hdecomp : (fun j => ((amSignal N A μ m k j : ℝ) : ℂ))
      = ((A : ℂ) / 2) • (fun j => stdAddChar (k * j))
        + ((A : ℂ) / 2) • (fun j => stdAddChar (-(k * j)))
        + (((μ : ℂ) / 2) • (fun j => stdAddChar (k * j) * (m j : ℂ))
          + ((μ : ℂ) / 2) • (fun j => stdAddChar (-(k * j)) * (m j : ℂ))) := by
    ext j
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, amSignal]
    push_cast
    rw [carrierCos_eq_stdAddChar]
    ring
  rw [hdecomp]
  simp only [map_add, Pi.add_apply, _root_.map_smul, Pi.smul_apply, smul_eq_mul]
  have hn1 : (fun j => stdAddChar (-(k * j))) = (fun j => stdAddChar ((-k) * j)) := by
    ext j
    rw [neg_mul]
  have hn2 : (fun j => stdAddChar (-(k * j)) * (m j : ℂ))
      = (fun j => stdAddChar ((-k) * j) * (m j : ℂ)) := by
    ext j
    rw [neg_mul]
  rw [hn1, hn2, dft_stdAddChar, dft_stdAddChar, dft_stdAddChar_mul, dft_stdAddChar_mul,
    sub_neg_eq_add]
  simp only [messageSpectrum]
  ring

/-- No-alias reading, positive shift: if the shifted supports are disjoint, a bin of
the positively shifted replica off the carrier bins carries exactly `μ / 2 · M (l - k)`. -/
lemma dft_amSignal_eq_positive_shift (N : ℕ) [NeZero N] (A μ : ℝ) (m : ZMod N → ℝ)
    (k l : ZMod N) (hdisj : Disjoint (positiveShiftSupport N m k) (negativeShiftSupport N m k))
    (hl : l ∈ positiveShiftSupport N m k) (hlk : l ≠ k) (hlnk : l ≠ -k) :
    𝓕 (fun j => ((amSignal N A μ m k j : ℝ) : ℂ)) l =
      (μ : ℂ) / 2 * messageSpectrum N m (l - k) := by
  rw [dft_amSignal]
  have e1 : (Pi.single k (1 : ℂ) : ZMod N → ℂ) l = 0 := by
    simp [Pi.single_apply, hlk]
  have e2 : (Pi.single (-k) (1 : ℂ) : ZMod N → ℂ) l = 0 := by
    simp [Pi.single_apply, hlnk]
  have hnot : l ∉ negativeShiftSupport N m k := Set.disjoint_left.mp hdisj hl
  have e3 : messageSpectrum N m (l + k) = 0 := by
    by_contra hne
    exact hnot hne
  rw [e1, e2, e3]
  ring

/-- No-alias reading, negative shift: the mirror statement for `M (l + k)`. -/
lemma dft_amSignal_eq_negative_shift (N : ℕ) [NeZero N] (A μ : ℝ) (m : ZMod N → ℝ)
    (k l : ZMod N) (hdisj : Disjoint (positiveShiftSupport N m k) (negativeShiftSupport N m k))
    (hl : l ∈ negativeShiftSupport N m k) (hlk : l ≠ k) (hlnk : l ≠ -k) :
    𝓕 (fun j => ((amSignal N A μ m k j : ℝ) : ℂ)) l =
      (μ : ℂ) / 2 * messageSpectrum N m (l + k) := by
  rw [dft_amSignal]
  have e1 : (Pi.single k (1 : ℂ) : ZMod N → ℂ) l = 0 := by
    simp [Pi.single_apply, hlk]
  have e2 : (Pi.single (-k) (1 : ℂ) : ZMod N → ℂ) l = 0 := by
    simp [Pi.single_apply, hlnk]
  have hnot : l ∉ positiveShiftSupport N m k :=
    Set.disjoint_right.mp hdisj hl
  have e3 : messageSpectrum N m (l - k) = 0 := by
    by_contra hne
    exact hnot hne
  rw [e1, e2, e3]
  ring

private theorem messageSpectrum_carrierCos_aux (N : ℕ) [NeZero N] (f l : ZMod N) :
    messageSpectrum N (carrierCos N f) l =
      (N : ℂ) / 2 * ((Pi.single f (1 : ℂ) : ZMod N → ℂ) l + (Pi.single (-f) (1 : ℂ) : ZMod N → ℂ) l) := by
  have hdecomp : (fun j => ((carrierCos N f j : ℝ) : ℂ))
      = ((1 / 2 : ℂ)) • (fun j => stdAddChar (f * j))
        + ((1 / 2 : ℂ)) • (fun j => stdAddChar (-(f * j))) := by
    ext j
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [carrierCos_eq_stdAddChar]
    ring
  show 𝓕 (fun j => ((carrierCos N f j : ℝ) : ℂ)) l = _
  rw [hdecomp]
  simp only [map_add, Pi.add_apply, _root_.map_smul, Pi.smul_apply, smul_eq_mul]
  have hn : (fun j => stdAddChar (-(f * j))) = (fun j => stdAddChar ((-f) * j)) := by
    ext j
    rw [neg_mul]
  rw [hn, dft_stdAddChar, dft_stdAddChar]
  ring

/-- Validation, constant message `m ≡ c`: only the carrier bins survive, with weight
`(A + μ c) N / 2`. -/
lemma dft_amSignal_const_message (N : ℕ) [NeZero N] (A μ c : ℝ) (k l : ZMod N) :
    𝓕 (fun j => ((amSignal N A μ (fun _ => c) k j : ℝ) : ℂ)) l =
      ((A + μ * c : ℝ) : ℂ) * (N : ℂ) / 2 * ((Pi.single k (1 : ℂ) : ZMod N → ℂ) l + (Pi.single (-k) (1 : ℂ) : ZMod N → ℂ) l) := by
  have hdecomp : (fun j => ((amSignal N A μ (fun _ => c) k j : ℝ) : ℂ))
      = (((A + μ * c : ℝ) : ℂ)) • (fun j => ((carrierCos N k j : ℝ) : ℂ)) := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, amSignal]
    push_cast
    ring
  rw [hdecomp, _root_.map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h := messageSpectrum_carrierCos_aux N k l
  unfold messageSpectrum at h
  rw [h]
  ring

/-- A baseband cosine tone at bin `f` has spectrum `N / 2` at `f` and `-f`. -/
lemma messageSpectrum_carrierCos (N : ℕ) [NeZero N] (f l : ZMod N) :
    messageSpectrum N (carrierCos N f) l =
      (N : ℂ) / 2 * ((Pi.single f (1 : ℂ) : ZMod N → ℂ) l + (Pi.single (-f) (1 : ℂ) : ZMod N → ℂ) l) := by
  exact messageSpectrum_carrierCos_aux N f l

/-- Validation, baseband tone at `f`: carrier impulses plus four sideband impulses at
`±k ± f`, each of weight `μ N / 4`. -/
lemma dft_amSignal_tone_message (N : ℕ) [NeZero N] (A μ : ℝ) (f k l : ZMod N) :
    𝓕 (fun j => ((amSignal N A μ (carrierCos N f) k j : ℝ) : ℂ)) l =
      (A : ℂ) * (N : ℂ) / 2 * ((Pi.single k (1 : ℂ) : ZMod N → ℂ) l + (Pi.single (-k) (1 : ℂ) : ZMod N → ℂ) l) +
        (μ : ℂ) * (N : ℂ) / 4 *
          ((Pi.single (k + f) (1 : ℂ) : ZMod N → ℂ) l + (Pi.single (k - f) (1 : ℂ) : ZMod N → ℂ) l +
            (Pi.single (-k + f) (1 : ℂ) : ZMod N → ℂ) l + (Pi.single (-k - f) (1 : ℂ) : ZMod N → ℂ) l) := by
  rw [dft_amSignal, messageSpectrum_carrierCos, messageSpectrum_carrierCos]
  have h1 : (Pi.single f (1 : ℂ) : ZMod N → ℂ) (l - k) = (Pi.single (k + f) (1 : ℂ) : ZMod N → ℂ) l := by
    by_cases h : l - k = f
    · have hl : l = k + f := by linear_combination h
      simp [Pi.single_apply, h, hl]
    · have hl : l ≠ k + f := fun he => h (by linear_combination he)
      simp [Pi.single_apply, h, hl]
  have h2 : (Pi.single (-f) (1 : ℂ) : ZMod N → ℂ) (l - k) = (Pi.single (k - f) (1 : ℂ) : ZMod N → ℂ) l := by
    by_cases h : l - k = -f
    · have hl : l = k - f := by linear_combination h
      simp [Pi.single_apply, h, hl]
    · have hl : l ≠ k - f := fun he => h (by linear_combination he)
      simp [Pi.single_apply, h, hl]
  have h3 : (Pi.single f (1 : ℂ) : ZMod N → ℂ) (l + k) = (Pi.single (-k + f) (1 : ℂ) : ZMod N → ℂ) l := by
    by_cases h : l + k = f
    · rw [h, show l = -k + f from by linear_combination h, Pi.single_eq_same, Pi.single_eq_same]
    · have hl : l ≠ -k + f := fun he => h (by linear_combination he)
      simp [Pi.single_apply, h, hl]
  have h4 : (Pi.single (-f) (1 : ℂ) : ZMod N → ℂ) (l + k) = (Pi.single (-k - f) (1 : ℂ) : ZMod N → ℂ) l := by
    by_cases h : l + k = -f
    · rw [h, show l = -k - f from by linear_combination h, Pi.single_eq_same, Pi.single_eq_same]
    · have hl : l ≠ -k - f := fun he => h (by linear_combination he)
      simp [Pi.single_apply, h, hl]
  rw [h1, h2, h3, h4]
  ring

/-- Violated premise, general: if `k + k = 0` (so `k = -k`) and the message spectrum is
not identically zero, the two shifted supports coincide and are not disjoint. -/
lemma not_disjoint_shifted_supports_of_add_self_eq_zero (N : ℕ) [NeZero N] (m : ZMod N → ℝ)
    (k : ZMod N) (hk : k + k = 0) (hm : ∃ l : ZMod N, messageSpectrum N m l ≠ 0) :
    ¬ Disjoint (positiveShiftSupport N m k) (negativeShiftSupport N m k) := by
  obtain ⟨l₀, hl₀⟩ := hm
  intro hdisj
  have hmemU : l₀ + k ∈ positiveShiftSupport N m k := by
    show messageSpectrum N m ((l₀ + k) - k) ≠ 0
    rw [add_sub_cancel_right]
    exact hl₀
  have hmemL : l₀ + k ∈ negativeShiftSupport N m k := by
    show messageSpectrum N m ((l₀ + k) + k) ≠ 0
    have heq : (l₀ + k) + k = l₀ := by rw [add_assoc, hk, add_zero]
    rw [heq]
    exact hl₀
  exact (Set.disjoint_left.mp hdisj hmemU) hmemL

/-- Violated premise, concrete: `N = 4`, carrier `k = 1`, message tone `f = 1`. The
upper and lower sidebands both occupy bins `0` and `2`. -/
lemma not_disjoint_shifted_supports_tone_four :
    ¬ Disjoint (positiveShiftSupport 4 (carrierCos 4 1) 1)
      (negativeShiftSupport 4 (carrierCos 4 1) 1) := by
  intro hdisj
  have h0u : (0 : ZMod 4) ∈ positiveShiftSupport 4 (carrierCos 4 1) 1 := by
    show messageSpectrum 4 (carrierCos 4 1) (0 - 1) ≠ 0
    rw [messageSpectrum_carrierCos]
    have e1 : ((0 : ZMod 4) - 1) ≠ 1 := by decide
    have e2 : ((0 : ZMod 4) - 1) = -1 := by decide
    rw [Pi.single_apply, Pi.single_apply, ite_eq_right e1, ite_eq_left e2]
    norm_num
  have h0l : (0 : ZMod 4) ∈ negativeShiftSupport 4 (carrierCos 4 1) 1 := by
    show messageSpectrum 4 (carrierCos 4 1) (0 + 1) ≠ 0
    rw [messageSpectrum_carrierCos]
    have e1 : ((0 : ZMod 4) + 1) = 1 := by decide
    have e2 : ((0 : ZMod 4) + 1) ≠ -1 := by decide
    rw [Pi.single_apply, Pi.single_apply, ite_eq_left e1, ite_eq_right e2]
    norm_num
  exact (Set.disjoint_left.mp hdisj h0u) h0l

/-- The overlapping case still obeys the identity: at bin `0` of the `N = 4`, `k = f = 1`
fixture both sidebands contribute and the DFT is `2 μ` (it is `A + μ - A + μ` summed
over the samples `A + μ, 0, μ - A, 0`). -/
lemma dft_amSignal_tone_four_zero (A μ : ℝ) :
    𝓕 (fun j => ((amSignal 4 A μ (carrierCos 4 1) 1 j : ℝ) : ℂ)) 0 = 2 * (μ : ℂ) := by
  rw [dft_amSignal_tone_message]
  have z1 : (Pi.single (1 : ZMod 4) (1 : ℂ) : ZMod 4 → ℂ) 0 = 0 := @Pi.single_eq_of_ne (ZMod 4) (fun _ => ℂ) _ _ 1 0 (by decide) (1 : ℂ)
  have z2 : (Pi.single (-1 : ZMod 4) (1 : ℂ) : ZMod 4 → ℂ) 0 = 0 := @Pi.single_eq_of_ne (ZMod 4) (fun _ => ℂ) _ _ (-1) 0 (by decide) (1 : ℂ)
  have z3 : (Pi.single (1 + 1 : ZMod 4) (1 : ℂ) : ZMod 4 → ℂ) 0 = 0 := @Pi.single_eq_of_ne (ZMod 4) (fun _ => ℂ) _ _ (1 + 1) 0 (by decide) (1 : ℂ)
  have z4 : (Pi.single (1 - 1 : ZMod 4) (1 : ℂ) : ZMod 4 → ℂ) 0 = 1 := by
    rw [show (1 - 1 : ZMod 4) = 0 by decide]
    exact @Pi.single_eq_same (ZMod 4) (fun _ => ℂ) _ _ 0 (1 : ℂ)
  have z5 : (Pi.single (-1 + 1 : ZMod 4) (1 : ℂ) : ZMod 4 → ℂ) 0 = 1 := by
    rw [show (-1 + 1 : ZMod 4) = 0 by decide]
    exact @Pi.single_eq_same (ZMod 4) (fun _ => ℂ) _ _ 0 (1 : ℂ)
  have z6 : (Pi.single (-1 - 1 : ZMod 4) (1 : ℂ) : ZMod 4 → ℂ) 0 = 0 := @Pi.single_eq_of_ne (ZMod 4) (fun _ => ℂ) _ _ (-1 - 1) 0 (by decide) (1 : ℂ)
  rw [z1, z2, z3, z4, z5, z6]
  push_cast
  ring

end PhyslibExt.Communications.FiniteAMModulator
