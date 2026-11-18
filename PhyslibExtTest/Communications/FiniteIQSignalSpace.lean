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

end PhyslibExtTest.Communications.FiniteIQSignalSpace
