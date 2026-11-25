/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Communications.FiniteIQSignalSpace

@[expose] public section

open PhyslibExt.Communications.FiniteIQSignalSpace

namespace PhyslibExtTest.Communications.FiniteIQSignalSpace

/-- The `sqrt(1/pi) * cos` waveform on `[0, 2pi]` is the in-phase
waveform at period `2 * pi` and carrier index `1`. -/
example (t : ℝ) :
    inPhaseWaveform (2 * Real.pi) 1 t = Real.sqrt (1 / Real.pi) * Real.cos t := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold inPhaseWaveform
  simp only [Nat.cast_one, mul_one]
  have h1 : (2 : ℝ) / (2 * Real.pi) = 1 / Real.pi := by
    field_simp
  have h2 : 2 * Real.pi * t / (2 * Real.pi) = t := by
    field_simp
  rw [h1, h2]

/-- The `sqrt(1/pi) * cos` unit-energy instance on `[0, 2pi]`: the
in-phase waveform at period `2 * pi` and carrier index `1` has unit
energy. -/
example :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      inPhaseWaveform (2 * Real.pi) 1 t * inPhaseWaveform (2 * Real.pi) 1 t) = 1 :=
  inPhaseWaveform_norm (2 * Real.pi) 1 (mul_pos (by norm_num) Real.pi_pos) le_rfl

/-- Cos/sin orthogonality on `[0, 2pi]`: the in-phase and quadrature
waveforms at period `2 * pi` and carrier index `1` are orthogonal. -/
example :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      inPhaseWaveform (2 * Real.pi) 1 t * quadratureWaveform (2 * Real.pi) 1 t) = 0 :=
  inPhaseWaveform_quadratureWaveform_orthogonal (2 * Real.pi) 1
    (mul_pos (by norm_num) Real.pi_pos) le_rfl

/-- The quadrature waveform at period `2 * pi` and carrier index `1`
has unit energy. -/
example :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      quadratureWaveform (2 * Real.pi) 1 t * quadratureWaveform (2 * Real.pi) 1 t) = 1 :=
  quadratureWaveform_norm (2 * Real.pi) 1 (mul_pos (by norm_num) Real.pi_pos) le_rfl

/-- The 3-4-25 coefficient arithmetic: coefficients `3` and `4` at
carrier index `1` give energy `25`. -/
example :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      iqWaveform 3 4 (2 * Real.pi) 1 t * iqWaveform 3 4 (2 * Real.pi) 1 t) = 25 :=
  iqWaveform_energy_firstCarrier_example (2 * Real.pi)
    (mul_pos (by norm_num) Real.pi_pos)

/-- Coefficients `3` and `4` at carrier index `2` project to `3` and
`4`. -/
example :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
        iqWaveform 3 4 (2 * Real.pi) 2 t * inPhaseWaveform (2 * Real.pi) 2 t) = 3 ∧
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        iqWaveform 3 4 (2 * Real.pi) 2 t * quadratureWaveform (2 * Real.pi) 2 t) = 4 :=
  iqWaveform_projection_secondCarrier_example (2 * Real.pi)
    (mul_pos (by norm_num) Real.pi_pos)

/-- The headline statement at period `2 * pi`, carrier index `1` and
coefficients `3` and `4`. -/
example :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
        inPhaseWaveform (2 * Real.pi) 1 t * inPhaseWaveform (2 * Real.pi) 1 t) = 1 ∧
      (∫ t in (0 : ℝ)..(2 * Real.pi),
          quadratureWaveform (2 * Real.pi) 1 t
            * quadratureWaveform (2 * Real.pi) 1 t) = 1 ∧
      (∫ t in (0 : ℝ)..(2 * Real.pi),
          inPhaseWaveform (2 * Real.pi) 1 t
            * quadratureWaveform (2 * Real.pi) 1 t) = 0 ∧
      (∫ t in (0 : ℝ)..(2 * Real.pi),
          iqWaveform 3 4 (2 * Real.pi) 1 t * iqWaveform 3 4 (2 * Real.pi) 1 t)
        = 3 ^ 2 + 4 ^ 2 ∧
      (∫ t in (0 : ℝ)..(2 * Real.pi),
          iqWaveform 3 4 (2 * Real.pi) 1 t * inPhaseWaveform (2 * Real.pi) 1 t) = 3 ∧
      (∫ t in (0 : ℝ)..(2 * Real.pi),
          iqWaveform 3 4 (2 * Real.pi) 1 t * quadratureWaveform (2 * Real.pi) 1 t) = 4 :=
  iqBasis_orthonormal_energy_and_projection 3 4 (2 * Real.pi) 1
    (mul_pos (by norm_num) Real.pi_pos) le_rfl

/-- A quarter-cycle carrier on the unit window is not orthogonal. -/
example :
    (∫ t in (0 : ℝ)..1, Real.cos (Real.pi * t / 2) * Real.sin (Real.pi * t / 2))
      ≠ 0 :=
  quarterCycleCarrier_crossIntegral_ne_zero

/-- Through the bridge lemmas, the existing quadrature-average result
for root-mean-square phasor waveforms gives the orthogonality of the
first-carrier in-phase and quadrature waveforms over one period. -/
example (T : ℝ) (hT : 0 < T) :
    (∫ t in (0 : ℝ)..(0 + 2 * Real.pi / (2 * Real.pi * ((1 : ℕ) : ℝ) / T)),
        inPhaseWaveform T 1 t * quadratureWaveform T 1 t)
        / (2 * Real.pi / (2 * Real.pi * ((1 : ℕ) : ℝ) / T)) = 0 := by
  simp only [inPhaseWaveform_eq_rmsWaveform, quadratureWaveform_eq_rmsWaveform]
  exact PhyslibExt.Circuits.RMSAveragePower.average_rmsWaveform_mul_quadrature
    (Real.sqrt (1 / T) : ℂ)
    (div_pos (mul_pos (mul_pos two_pos Real.pi_pos) (by norm_num)) hT) 0

/-- Through the bridge lemma, the existing self-average result for
root-mean-square phasor waveforms gives the first-carrier combined
waveform the mean power `(a ^ 2 + b ^ 2) / T` over one period,
matching its energy `a ^ 2 + b ^ 2` on `[0, T]`. -/
example (a b T : ℝ) (hT : 0 < T) :
    (∫ t in (0 : ℝ)..(0 + 2 * Real.pi / (2 * Real.pi * ((1 : ℕ) : ℝ) / T)),
        iqWaveform a b T 1 t * iqWaveform a b T 1 t)
        / (2 * Real.pi / (2 * Real.pi * ((1 : ℕ) : ℝ) / T)) = (a ^ 2 + b ^ 2) / T := by
  simp only [iqWaveform_eq_rmsWaveform]
  rw [PhyslibExt.Circuits.RMSAveragePower.average_rmsWaveform_mul_self_re_im _
    (div_pos (mul_pos (mul_pos two_pos Real.pi_pos) (by norm_num)) hT) 0]
  have hs : Real.sqrt (1 / T) ^ 2 = 1 / T := Real.sq_sqrt (by positivity)
  rw [show (a ^ 2 + b ^ 2) / T = (a ^ 2 + b ^ 2) * Real.sqrt (1 / T) ^ 2 by
    rw [hs]; ring]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

end PhyslibExtTest.Communications.FiniteIQSignalSpace
