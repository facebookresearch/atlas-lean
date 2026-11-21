/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.OscillatorResponse
import PhyslibExt.EarthScience.DampedOscillator
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Oscillator parameter correspondence, forced response and resonance checks

Concrete consumers of `PhyslibExt.Mechanics.OscillatorResponse`: the critically damped
mass-spring-damper `m = 1`, `c = 2`, `k = 1` with initial data `x₀ = v₀ = 1`, the boundary
cases of the parameter map, the forced response of the same system to `25 cos (2 t)` from
`x₀ = 0`, `v₀ = 1`, the excluded undamped exact resonance, and the secular response `t sin t`
of `x'' + x = 2 cos t` at that resonance.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Critical damping and conventions
- B. Forced response
- C. Undamped resonance

## iv. References

None.

## A. Critical damping and conventions

-/

open ClassicalMechanics Time ContDiff PhyslibExt.Mechanics.OscillatorResponse

/-- Critical damping with nonzero initial data: `m = 1`, `c = 2`, `k = 1` (`c ^ 2 = 4 m k`),
`x₀ = v₀ = 1`. Both conventions give the rate `1`, and the free trajectory is
`exp (-t) (1 + 2 t)`. -/
example :
    (massSpringDamper 1 2 1 one_pos zero_le_two one_pos).IsCriticallyDamped ∧
      atlasDamping 1 2 = 1 ∧ atlasNaturalFrequency 1 1 = 1 ∧
      ∀ t : Time, (massSpringDamper 1 2 1 one_pos zero_le_two one_pos).trajectory
          (initialConditions 1 1) t =
        Real.exp (-(t : ℝ)) • EuclideanSpace.single 0 (1 + 2 * (t : ℝ)) := by
  set S := massSpringDamper 1 2 1 one_pos zero_le_two one_pos
  have hcrit : S.IsCriticallyDamped := by
    change (2 : ℝ) ^ 2 - 4 * 1 * 1 = 0
    norm_num
  refine ⟨hcrit, by norm_num [atlasDamping], by norm_num [atlasNaturalFrequency], fun t => ?_⟩
  rw [S.trajectory_eq_of_criticallyDamped _ hcrit]
  have hd : S.decayRate = 1 := by
    change (2 : ℝ) / (2 * 1) = 1
    norm_num
  simp only [DampedHarmonicOscillator.criticallyDampedBase, initialConditions, hd]
  ext i
  fin_cases i
  simp
  ring

/-- Boundary cases: no Physlib oscillator has `k = 0`; for `m = 1`, `c = 2` the Physlib damping
coefficient is `2` while the convention's damping rate is `1` (the factor `2 m`); a force
amplitude `4` on mass `2` is the acceleration amplitude `2`. -/
example :
    (¬ ∃ S : DampedHarmonicOscillator, S.k = 0) ∧
      (massSpringDamper 1 2 1 one_pos zero_le_two one_pos).γ = 2 ∧ atlasDamping 1 2 = 1 ∧
      atlasForcing 2 4 = 2 := by
  exact ⟨fun ⟨S, hS⟩ => S.k_ne_zero hS, rfl, by norm_num [atlasDamping],
    by norm_num [atlasForcing]⟩

/-! ## B. Forced response -/

/-- Nonzero forcing and nonzero initial velocity: `m = 1`, `c = 2`, `k = 1` (critical damping),
`F = 25`, `Ω = 2`, `x₀ = 0`, `v₀ = 1`. The denominator is `25`, the particular response
`-3 cos (2 t) + 4 sin (2 t)` (`x_p (0) = -3`, `x_p' (0) = 8`), the corrected free data are
`(3, -7)` and the response is `-3 cos (2 t) + 4 sin (2 t) + e^{-t} (3 - 4 t)`. -/
example :
    steadyStateDenominator 1 2 1 2 = 25 ∧
      (∀ t, particularResponse 1 2 1 25 2 t = -3 * Real.cos (2 * t) + 4 * Real.sin (2 * t)) ∧
      ∀ t, forcedResponse 1 2 1 one_pos zero_le_two one_pos 25 2 0 1 t =
        -3 * Real.cos (2 * t) + 4 * Real.sin (2 * t) + Real.exp (-t) * (3 - 4 * t) := by
  have hD : steadyStateDenominator 1 2 1 2 = 25 := by norm_num [steadyStateDenominator]
  have hA : steadyStateCos 1 2 1 25 2 = -3 := by
    norm_num [steadyStateCos, steadyStateDenominator]
  have hB : steadyStateSin 1 2 1 25 2 = 4 := by
    norm_num [steadyStateSin, steadyStateDenominator]
  refine ⟨hD, fun t => by simp only [particularResponse, hA, hB], fun t => ?_⟩
  -- The explicit response is a `C²` solution with the initial data `(0, 1)`, so uniqueness
  -- identifies it with the forced response.
  set y : ℝ → ℝ := fun s =>
    -3 * Real.cos (2 * s) + 4 * Real.sin (2 * s) + Real.exp (-s) * (3 - 4 * s) with hy
  have h2 : ∀ s : ℝ, HasDerivAt (fun r : ℝ => 2 * r) 2 s := fun s => by
    simpa using (hasDerivAt_id s).const_mul (2 : ℝ)
  have he : ∀ s : ℝ, HasDerivAt (fun r : ℝ => Real.exp (-r)) (-Real.exp (-s)) s := fun s =>
    ((Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)).congr_deriv (by ring)
  have hl : ∀ s : ℝ, HasDerivAt (fun r : ℝ => 3 - 4 * r) (-4) s := fun s => by
    simpa using ((hasDerivAt_id s).const_mul (4 : ℝ)).const_sub 3
  have hl' : ∀ s : ℝ, HasDerivAt (fun r : ℝ => 4 * r - 7) 4 s := fun s => by
    simpa using ((hasDerivAt_id s).const_mul (4 : ℝ)).sub_const 7
  have hy1 : ∀ s, HasDerivAt y
      (6 * Real.sin (2 * s) + 8 * Real.cos (2 * s) + Real.exp (-s) * (4 * s - 7)) s := by
    intro s
    have h := ((((Real.hasDerivAt_cos (2 * s)).comp s (h2 s)).const_mul (-3)).add
      (((Real.hasDerivAt_sin (2 * s)).comp s (h2 s)).const_mul 4)).add ((he s).mul (hl s))
    exact h.congr_deriv (by ring)
  have hy2 : ∀ s, HasDerivAt
      (fun r => 6 * Real.sin (2 * r) + 8 * Real.cos (2 * r) + Real.exp (-r) * (4 * r - 7))
      (12 * Real.cos (2 * s) - 16 * Real.sin (2 * s) + Real.exp (-s) * (11 - 4 * s)) s := by
    intro s
    have h := ((((Real.hasDerivAt_sin (2 * s)).comp s (h2 s)).const_mul 6).add
      (((Real.hasDerivAt_cos (2 * s)).comp s (h2 s)).const_mul 8)).add ((he s).mul (hl' s))
    exact h.congr_deriv (by ring)
  have hd1 : deriv y =
      fun s => 6 * Real.sin (2 * s) + 8 * Real.cos (2 * s) + Real.exp (-s) * (4 * s - 7) :=
    funext fun s => (hy1 s).deriv
  have hyC : ContDiff ℝ 2 y := by
    rw [hy]
    fun_prop
  have hEq : ∀ s : ℝ, 1 * deriv (deriv y) s + 2 * deriv y s + 1 * y s =
      25 * Real.cos (2 * s) := by
    intro s
    rw [hd1, (hy2 s).deriv]
    simp only [hy]
    ring
  have hu := forcedResponse_unique (x₀ := 0) (v₀ := 1) one_pos zero_le_two one_pos
    (by rw [hD]; norm_num) hyC hEq (by simp [hy]) (by rw [hd1]; norm_num)
  exact (congrFun hu t).symm

/-- Amplitude algebra is not an ODE certificate: for the same system the steady-state amplitude
`√(A ^ 2 + B ^ 2)` is `5`, but `5 cos (2 t)` (right amplitude, no phase) does not solve the
forced equation; at `t = 0` its left side is `-15`, not `25`. -/
example :
    Real.sqrt (steadyStateCos 1 2 1 25 2 ^ 2 + steadyStateSin 1 2 1 25 2 ^ 2) = 5 ∧
      ¬ ∀ t : ℝ, 1 * deriv (deriv (fun s : ℝ => 5 * Real.cos (2 * s))) t +
          2 * deriv (fun s : ℝ => 5 * Real.cos (2 * s)) t + 1 * (5 * Real.cos (2 * t)) =
        25 * Real.cos (2 * t) := by
  -- The amplitude through the forced-oscillator convention and its existing amplitude formula.
  obtain ⟨hA, hB⟩ := steadyState_coefficients_convention (c := 2) one_pos zero_le_one 25 2
  have hω : atlasNaturalFrequency 1 1 = 1 := by norm_num [atlasNaturalFrequency]
  have hγ : atlasDamping 1 2 = 1 := by norm_num [atlasDamping]
  have hf : atlasForcing 1 25 = 25 := by norm_num [atlasForcing]
  have hpos : 0 < (atlasNaturalFrequency 1 1 ^ 2 - 2 ^ 2) ^ 2 + (2 * atlasDamping 1 2 * 2) ^ 2 := by
    rw [hω, hγ]
    norm_num
  refine ⟨?_, fun h => ?_⟩
  · rw [hA, hB, EarthScience.damped_oscillator_amplitude hpos, hω, hγ, hf,
      show ((1 : ℝ) ^ 2 - 2 ^ 2) ^ 2 + (2 * 1 * 2) ^ 2 = 5 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    norm_num
  · have h2 : ∀ s : ℝ, HasDerivAt (fun r : ℝ => 2 * r) 2 s := fun s => by
      simpa using (hasDerivAt_id s).const_mul (2 : ℝ)
    have hy : ∀ s : ℝ,
        HasDerivAt (fun r : ℝ => 5 * Real.cos (2 * r)) (-10 * Real.sin (2 * s)) s := fun s =>
      (((Real.hasDerivAt_cos (2 * s)).comp s (h2 s)).const_mul 5).congr_deriv (by ring)
    have hy' : ∀ s : ℝ,
        HasDerivAt (fun r : ℝ => -10 * Real.sin (2 * r)) (-20 * Real.cos (2 * s)) s := fun s =>
      (((Real.hasDerivAt_sin (2 * s)).comp s (h2 s)).const_mul (-10)).congr_deriv (by ring)
    have hd : deriv (fun s : ℝ => 5 * Real.cos (2 * s)) = fun s => -10 * Real.sin (2 * s) :=
      funext fun s => (hy s).deriv
    have h0 := h 0
    rw [hd, (hy' 0).deriv] at h0
    norm_num at h0

/-- The excluded branch: at `c = 0`, `k = m Ω ^ 2` (`m = k = Ω = F = 1`) the denominator is `0`,
the coefficient formulas collapse to `0` (division by zero), and the zero function does not
solve `x'' + x = cos t`. -/
example :
    steadyStateDenominator 1 0 1 1 = 0 ∧ (∀ t, particularResponse 1 0 1 1 1 t = 0) ∧
      ¬ ∀ t, 1 * deriv (deriv (particularResponse 1 0 1 1 1)) t +
          0 * deriv (particularResponse 1 0 1 1 1) t + 1 * particularResponse 1 0 1 1 1 t =
        1 * Real.cos (1 * t) := by
  have hD : steadyStateDenominator 1 0 1 1 = 0 :=
    not_not.mp fun h => (steadyStateDenominator_ne_zero_iff one_pos 1).mp h ⟨rfl, by norm_num⟩
  have hp : ∀ t, particularResponse 1 0 1 1 1 t = 0 := fun t => by
    simp [particularResponse, steadyStateCos, steadyStateSin, hD]
  refine ⟨hD, hp, fun h => ?_⟩
  have h0 := h 0
  rw [show particularResponse 1 0 1 1 1 = fun _ => 0 from funext hp] at h0
  simp at h0

/-! ## C. Undamped resonance -/

/-- Growth fixture: `m = ω₀ = k = 1` and `F = 2` give `x (t) = t sin t`; at the envelope-touch
times `t_n = 2 π n + π / 2` the response equals `t_n`, a strictly increasing sequence. -/
example :
    (∀ t, resonantResponse 1 1 2 t = t * Real.sin t) ∧
      (∀ n : ℕ,
        resonantResponse 1 1 2 (resonanceEnvelopeTime 1 n) = 2 * Real.pi * n + Real.pi / 2) ∧
      StrictMono (fun n : ℕ => resonantResponse 1 1 2 (resonanceEnvelopeTime 1 n)) := by
  have h2 : ∀ n : ℕ, resonantResponse 1 1 2 (resonanceEnvelopeTime 1 n)
      = 2 * Real.pi * n + Real.pi / 2 := by
    intro n
    rw [resonantResponse_resonanceEnvelopeTime zero_lt_one 1 2 n]
    unfold resonanceEnvelopeTime
    ring
  refine ⟨?_, h2, ?_⟩
  · intro t
    unfold resonantResponse
    rw [one_mul]
    ring
  · simp only [h2]
    apply strictMono_nat_of_lt_succ
    intro n
    push_cast
    have hpi := Real.pi_pos
    linarith

/-- Envelope contact with a negative force amplitude: for `m = ω₀ = 1` and `F = -2` the response
at the first envelope-touch time `t₀ = π / 2` is `-π / 2`, and its absolute value `π / 2` is the
envelope `|F| |t₀| / (2 m ω₀)`. -/
example :
    resonantResponse 1 1 (-2) (resonanceEnvelopeTime 1 0) = -(Real.pi / 2) ∧
      |resonantResponse 1 1 (-2) (resonanceEnvelopeTime 1 0)| =
        |(-2 : ℝ)| * |resonanceEnvelopeTime 1 0| / (2 * 1 * 1) ∧
      |resonantResponse 1 1 (-2) (resonanceEnvelopeTime 1 0)| = Real.pi / 2 := by
  have hval : resonantResponse 1 1 (-2) (resonanceEnvelopeTime 1 0) = -(Real.pi / 2) := by
    rw [resonantResponse_resonanceEnvelopeTime one_pos 1 (-2) 0]
    simp only [resonanceEnvelopeTime]
    push_cast
    ring
  refine ⟨hval, abs_resonantResponse_resonanceEnvelopeTime one_pos one_pos (-2) 0, ?_⟩
  rw [hval, abs_neg, abs_of_pos (by positivity)]

/-- Damped boundary: for `m = ω₀ = k = 1` and `F = 2` the resonant velocity at `t = π / 2` is `1`,
so with damping `c = 1` the term `c x'` is not cancelled and the damped equation fails. -/
example :
    deriv (resonantResponse 1 1 2) (Real.pi / 2) = 1 ∧
      ¬ ∀ t, 1 * deriv (deriv (resonantResponse 1 1 2)) t + 1 * deriv (resonantResponse 1 1 2) t +
        1 * resonantResponse 1 1 2 t = 2 * Real.cos (1 * t) := by
  constructor
  · rw [(hasDerivAt_resonantResponse 1 1 2 (Real.pi / 2)).deriv]
    unfold resonantVelocity
    rw [one_mul, Real.sin_pi_div_two, Real.cos_pi_div_two]
    norm_num
  · exact resonantResponse_not_solves_damped (m := 1) (ω₀ := 1) (k := 1) zero_lt_one zero_lt_one
      (by norm_num) (c := 1) (F := 2) one_ne_zero two_ne_zero
