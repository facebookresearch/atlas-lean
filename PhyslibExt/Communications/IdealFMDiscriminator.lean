/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Ideal FM discriminator and instantaneous frequency

## i. Overview

Frequency modulation with an ideal discriminator: for a continuous
message `m`, the FM signal with instantaneous frequency
`fc + kf m(t)` has constant modulus, and the division-based
discriminator recovers exactly `fc + kf m(t)`. The message is
therefore recoverable when `kf ≠ 0`; at zero amplitude the
discriminator outputs `0`, and at `kf = 0` every message gives the
same signal. Negative nonzero amplitudes are allowed and work
identically.

## ii. Key results

- `fmDiscriminator_eq_instantaneousFrequency`: the discriminator
  reads the instantaneous frequency (also in a `ContinuousOn`
  variant).
- `norm_fmSignal`: the signal has constant modulus.
- `fmMessage_eq_of_discriminator` and
  `fmSignal_message_injective`: message recovery.
- `discriminatorOutput_fmSignal_zero_amplitude` and
  `fmSignal_zero_sensitivity_eq`: the two failure modes.

## iii. Table of contents

- A. The FM signal and discriminator

## iv. References

- B. P. Lathi and Z. Ding, *Modern Digital and Analog Communication
Systems*, fifth edition, Oxford University Press, 2019: frequency modulation and discrimination.

## A. The FM signal and discriminator
-/

@[expose] public section

namespace PhyslibExt.Communications.IdealFMDiscriminator

open Complex

/-- FM phase `θ(t) = 2π f_c t + 2π k_f ∫_0^t m(s) ds` (oriented interval integral). -/
noncomputable def fmPhase (fc kf : ℝ) (m : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * Real.pi * fc * t + 2 * Real.pi * kf * ∫ s in (0 : ℝ)..t, m s

/-- Complex FM signal `z(t) = A · exp(i θ(t))`. -/
noncomputable def fmSignal (A fc kf : ℝ) (m : ℝ → ℝ) (t : ℝ) : ℂ :=
  (A : ℂ) * Complex.exp (Complex.I * (fmPhase fc kf m t : ℂ))

/-- Ideal frequency discriminator applied to a complex signal `z`:
`Im(conj(z t) · z'(t)) / (2π ‖z t‖²)`. It uses the derivative of `z`, never a phase
unwrap. The quotient is totalized in two ways: when `z t = 0`
the denominator vanishes and the value is `0` by the real-division
convention; and when `z` is not differentiable at `t`, the
totalized derivative `deriv z t` is `0`, so the value is again
`0`. No frequency is measured in either case, and every recovery
result below assumes a nonzero envelope and the needed
differentiability. -/
noncomputable def discriminatorOutput (z : ℝ → ℂ) (t : ℝ) : ℝ :=
  (starRingEnd ℂ (z t) * deriv z t).im / (2 * Real.pi * ‖z t‖ ^ 2)

/-- Phase derivative from the derivative of `t ↦ ∫ s in 0..t, m s`. -/
private theorem hasDerivAt_fmPhase_of_hasDerivAt_integral (fc kf : ℝ) (m : ℝ → ℝ)
    (t : ℝ) (hInt : HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, m s) (m t) t) :
    HasDerivAt (fmPhase fc kf m) (2 * Real.pi * fc + 2 * Real.pi * kf * m t) t := by
  have hlin : HasDerivAt (fun y : ℝ => 2 * Real.pi * fc * y) (2 * Real.pi * fc) t :=
    hasDerivAt_const_mul (2 * Real.pi * fc)
  have hint : HasDerivAt (fun y : ℝ => 2 * Real.pi * kf * ∫ s in (0 : ℝ)..y, m s)
      ((2 * Real.pi * kf) * m t) t :=
    HasDerivAt.const_mul (2 * Real.pi * kf) hInt
  have hadd : HasDerivAt
      (fun y : ℝ => 2 * Real.pi * fc * y + 2 * Real.pi * kf * ∫ s in (0 : ℝ)..y, m s)
      (2 * Real.pi * fc + (2 * Real.pi * kf) * m t) t :=
    hlin.add hint
  have heq : 2 * Real.pi * fc + (2 * Real.pi * kf) * m t
      = 2 * Real.pi * fc + 2 * Real.pi * kf * m t := by ring
  rw [heq] at hadd
  exact hadd

/-- Signal derivative from the phase derivative. -/
private theorem hasDerivAt_fmSignal_of_hasDerivAt_fmPhase (A fc kf : ℝ) (m : ℝ → ℝ)
    (t : ℝ)
    (hphase : HasDerivAt (fmPhase fc kf m)
      (2 * Real.pi * fc + 2 * Real.pi * kf * m t) t) :
    HasDerivAt (fmSignal A fc kf m)
      (Complex.I * ((2 * Real.pi * (fc + kf * m t) : ℝ) : ℂ)
        * fmSignal A fc kf m t) t := by
  have h1 : HasDerivAt (fun y : ℝ => ((fmPhase fc kf m y : ℝ) : ℂ))
      (((2 * Real.pi * fc + 2 * Real.pi * kf * m t : ℝ)) : ℂ) t :=
    hphase.ofReal_comp
  have h2 : HasDerivAt (fun y : ℝ => Complex.I * ((fmPhase fc kf m y : ℝ) : ℂ))
      (Complex.I * (((2 * Real.pi * fc + 2 * Real.pi * kf * m t : ℝ)) : ℂ)) t :=
    HasDerivAt.const_mul Complex.I h1
  have h3 := HasDerivAt.cexp h2
  have h4 := HasDerivAt.const_mul ((A : ℝ) : ℂ) h3
  have hrr : (2 * Real.pi * fc + 2 * Real.pi * kf * m t : ℝ)
      = 2 * Real.pi * (fc + kf * m t) := by ring
  have hDeq : (A : ℂ) * (Complex.exp (Complex.I * ((fmPhase fc kf m t : ℝ) : ℂ))
      * (Complex.I * (((2 * Real.pi * fc + 2 * Real.pi * kf * m t : ℝ)) : ℂ)))
      = Complex.I * ((2 * Real.pi * (fc + kf * m t) : ℝ) : ℂ)
        * ((A : ℂ) * Complex.exp (Complex.I * ((fmPhase fc kf m t : ℝ) : ℂ))) := by
    rw [hrr]
    ring
  have h4' : HasDerivAt
      (fun y : ℝ => (A : ℂ) * Complex.exp (Complex.I * ((fmPhase fc kf m y : ℝ) : ℂ)))
      ((A : ℂ) * (Complex.exp (Complex.I * ((fmPhase fc kf m t : ℝ) : ℂ))
        * (Complex.I * (((2 * Real.pi * fc + 2 * Real.pi * kf * m t : ℝ)) : ℂ)))) t :=
    h4
  rw [hDeq] at h4'
  exact h4'

/-- Constant envelope from `‖exp (I * θ)‖ = 1`. -/
private theorem norm_fmSignal_aux (A fc kf : ℝ) (m : ℝ → ℝ) (t : ℝ) :
    ‖fmSignal A fc kf m t‖ = |A| := by
  simp [fmSignal, Real.norm_eq_abs]

/-- Discriminator identity from the signal derivative. -/
private theorem fmDiscriminator_of_hasDerivAt_fmSignal (A fc kf : ℝ) (m : ℝ → ℝ)
    (t : ℝ) (hA : A ≠ 0)
    (hderiv : HasDerivAt (fmSignal A fc kf m)
      (Complex.I * ((2 * Real.pi * (fc + kf * m t) : ℝ) : ℂ)
        * fmSignal A fc kf m t) t) :
    discriminatorOutput (fmSignal A fc kf m) t = fc + kf * m t := by
  have hnorm : ‖fmSignal A fc kf m t‖ = |A| :=
    norm_fmSignal_aux A fc kf m t
  have hderiv_eq : deriv (fmSignal A fc kf m) t
      = Complex.I * ((2 * Real.pi * (fc + kf * m t) : ℝ) : ℂ)
        * fmSignal A fc kf m t :=
    hderiv.deriv
  have hmul : starRingEnd ℂ (fmSignal A fc kf m t)
        * (Complex.I * ((2 * Real.pi * (fc + kf * m t) : ℝ) : ℂ)
          * fmSignal A fc kf m t)
      = (((((|A|) ^ 2 * (2 * Real.pi * (fc + kf * m t)) : ℝ))) : ℂ) * Complex.I := by
    have h1 : starRingEnd ℂ (fmSignal A fc kf m t) * fmSignal A fc kf m t
        = ((((‖fmSignal A fc kf m t‖ : ℝ))) : ℂ) ^ 2 :=
      RCLike.conj_mul _
    rw [hnorm] at h1
    have h2 : starRingEnd ℂ (fmSignal A fc kf m t)
          * (Complex.I * ((2 * Real.pi * (fc + kf * m t) : ℝ) : ℂ)
            * fmSignal A fc kf m t)
        = (starRingEnd ℂ (fmSignal A fc kf m t) * fmSignal A fc kf m t)
          * (Complex.I * ((2 * Real.pi * (fc + kf * m t) : ℝ) : ℂ)) := by ring
    rw [h2, h1]
    push_cast
    ring
  have him : ∀ r : ℝ, (((r : ℝ) : ℂ) * Complex.I).im = r := by
    intro r
    simp
  unfold discriminatorOutput
  rw [hderiv_eq, hnorm, hmul, him]
  have hD : (2 : ℝ) * Real.pi * |A| ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (pow_ne_zero 2 (abs_ne_zero.mpr hA))
  rw [div_eq_iff hD]
  ring

/-- The FM phase has derivative `2π f_c + 2π k_f m(t)` for continuous `m`. -/
theorem hasDerivAt_fmPhase (fc kf : ℝ) (m : ℝ → ℝ) (hm : Continuous m) (t : ℝ) :
    HasDerivAt (fmPhase fc kf m) (2 * Real.pi * fc + 2 * Real.pi * kf * m t) t := by
  exact hasDerivAt_fmPhase_of_hasDerivAt_integral fc kf m t
    (hm.integral_hasStrictDerivAt 0 t).hasDerivAt

/-- The complex FM signal has derivative `i · 2π (f_c + k_f m(t)) · z(t)`. -/
lemma hasDerivAt_fmSignal (A fc kf : ℝ) (m : ℝ → ℝ) (hm : Continuous m) (t : ℝ) :
    HasDerivAt (fmSignal A fc kf m)
      (Complex.I * ((2 * Real.pi * (fc + kf * m t) : ℝ) : ℂ) * fmSignal A fc kf m t) t := by
  exact hasDerivAt_fmSignal_of_hasDerivAt_fmPhase A fc kf m t
    (hasDerivAt_fmPhase fc kf m hm t)

/-- Constant envelope: `‖z(t)‖ = |A|`. -/
lemma norm_fmSignal (A fc kf : ℝ) (m : ℝ → ℝ) (t : ℝ) :
    ‖fmSignal A fc kf m t‖ = |A| := by
  exact norm_fmSignal_aux A fc kf m t

/-- Ideal discriminator identity:
`Im(conj(z) z') / (2π ‖z‖²) = f_c + k_f m(t)` for `A ≠ 0` and continuous `m`. -/
lemma fmDiscriminator_eq_instantaneousFrequency (A fc kf : ℝ) (m : ℝ → ℝ)
    (hA : A ≠ 0) (hm : Continuous m) (t : ℝ) :
    discriminatorOutput (fmSignal A fc kf m) t = fc + kf * m t := by
  exact fmDiscriminator_of_hasDerivAt_fmSignal A fc kf m t hA
    (hasDerivAt_fmSignal A fc kf m hm t)

/-- Interval reading of the hypotheses: a message continuous on `[0, T]` gives the
same discriminator identity at every interior time `t ∈ (0, T)`. -/
lemma fmDiscriminator_eq_instantaneousFrequency_of_continuousOn (A fc kf T : ℝ)
    (m : ℝ → ℝ) (hA : A ≠ 0) (hm : ContinuousOn m (Set.Icc 0 T)) (t : ℝ)
    (ht : t ∈ Set.Ioo 0 T) :
    discriminatorOutput (fmSignal A fc kf m) t = fc + kf * m t := by
  have hle : (0 : ℝ) ≤ t := le_of_lt ht.1
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T :=
    Set.Icc_subset_Icc le_rfl (le_of_lt ht.2)
  have hint : IntervalIntegrable m MeasureTheory.volume 0 t :=
    (hm.mono hsub).intervalIntegrable_of_Icc hle
  have hcont : ContinuousAt m t := hm.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hmeas : StronglyMeasurableAtFilter m (nhds t) MeasureTheory.volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hm.mono Set.Ioo_subset_Icc_self) t ht
  have hInt : HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, m s) (m t) t :=
    (intervalIntegral.integral_hasStrictDerivAt_right hint hmeas hcont).hasDerivAt
  exact fmDiscriminator_of_hasDerivAt_fmSignal A fc kf m t hA
    (hasDerivAt_fmSignal_of_hasDerivAt_fmPhase A fc kf m t
      (hasDerivAt_fmPhase_of_hasDerivAt_integral fc kf m t hInt))

/-- Ideal demodulation for `k_f ≠ 0`:
`m(t) = (discriminatorOutput z t - f_c) / k_f`. -/
lemma fmMessage_eq_of_discriminator (A fc kf : ℝ) (m : ℝ → ℝ) (hA : A ≠ 0)
    (hkf : kf ≠ 0) (hm : Continuous m) (t : ℝ) :
    m t = (discriminatorOutput (fmSignal A fc kf m) t - fc) / kf := by
  have h := fmDiscriminator_eq_instantaneousFrequency A fc kf m hA hm t
  rw [h, eq_div_iff hkf]
  ring

/-- For `A ≠ 0` and `k_f ≠ 0`, the FM signal determines the continuous message. -/
lemma fmSignal_message_injective (A fc kf : ℝ) (m m' : ℝ → ℝ) (hA : A ≠ 0)
    (hkf : kf ≠ 0) (hm : Continuous m) (hm' : Continuous m')
    (h : fmSignal A fc kf m = fmSignal A fc kf m') :
    m = m' := by
  apply funext
  intro t
  have e1 := fmMessage_eq_of_discriminator A fc kf m hA hkf hm t
  have e2 := fmMessage_eq_of_discriminator A fc kf m' hA hkf hm' t
  have hdisc : discriminatorOutput (fmSignal A fc kf m) t
      = discriminatorOutput (fmSignal A fc kf m') t := by rw [h]
  rw [hdisc] at e1
  rw [e1, e2]

/-- Zero message: the discriminator reads the carrier frequency `f_c`. -/
lemma fmDiscriminator_zero_message (A fc kf : ℝ) (hA : A ≠ 0) (t : ℝ) :
    discriminatorOutput (fmSignal A fc kf (fun _ => 0)) t = fc := by
  simpa using fmDiscriminator_eq_instantaneousFrequency A fc kf (fun _ => 0) hA
    continuous_const t

/-- Constant message `c`: the discriminator reads `f_c + k_f c`. -/
lemma fmDiscriminator_const_message (A fc kf c : ℝ) (hA : A ≠ 0) (t : ℝ) :
    discriminatorOutput (fmSignal A fc kf (fun _ => c)) t = fc + kf * c := by
  exact fmDiscriminator_eq_instantaneousFrequency A fc kf (fun _ => c) hA
    continuous_const t

/-- Nonconstant continuous message `m = cos`: the discriminator reads
`f_c + k_f cos t`. -/
lemma fmDiscriminator_cos_message (A fc kf : ℝ) (hA : A ≠ 0) (t : ℝ) :
    discriminatorOutput (fmSignal A fc kf Real.cos) t = fc + kf * Real.cos t := by
  exact fmDiscriminator_eq_instantaneousFrequency A fc kf Real.cos hA
    Real.continuous_cos t

/-- `A = 0`: the signal is identically zero, so discrimination is
undefined; the totalized discriminator expression evaluates to `0`
only by the `0 / 0 = 0` convention, and no frequency is recovered. -/
lemma discriminatorOutput_fmSignal_zero_amplitude (fc kf : ℝ) (m : ℝ → ℝ) (t : ℝ) :
    discriminatorOutput (fmSignal 0 fc kf m) t = 0 := by
  have hz : fmSignal 0 fc kf m t = 0 := by simp [fmSignal]
  simp [discriminatorOutput, hz]

/-- `k_f = 0`: every message produces the same signal, so no message can be recovered. -/
lemma fmSignal_zero_sensitivity_eq (A fc : ℝ) (m m' : ℝ → ℝ) :
    fmSignal A fc 0 m = fmSignal A fc 0 m' := by
  apply funext
  intro t
  have hph : ∀ m : ℝ → ℝ, fmPhase fc 0 m t = 2 * Real.pi * fc * t := by
    intro m
    unfold fmPhase
    ring
  simp [fmSignal, hph]

end PhyslibExt.Communications.IdealFMDiscriminator
