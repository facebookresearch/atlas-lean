/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Biophysics.FitzHughNagumo

/-! Tests for the FitzHugh–Nagumo model with the concrete parameters `a = 6/5`, `b = 4/5`, `I = 0`
(FitzHugh's `b = 0.8`; `a` chosen so that the rest state is rational): the rest state
`(v*, w*) = (-3/2, -3/8)` and its uniqueness, its linearization type, the trapping ellipse checked
pointwise on its boundary from the definitions (and a non-trapping small ellipse), boundary probes
of the classification (center, saddle), and pulses after which the voltage falls or rises, both
by the definitions and through the full dynamics (`single_pulse_response` along solutions given
by `exists_isSolution`, with `ε = 10⁻⁵`); return to rest from a basin of that rest state and, for a
rest state with `v*² > 4`, from every initial state; and the exclusion of periodic orbits for
`v*² ≥ 4`, with boundary probes at `v*² = 4`. -/

open Real Set Filter
open scoped Topology

namespace MathlibExtTest.Biology.Biophysics.FitzHughNagumo

open MathlibExt.Biology.Biophysics.FitzHughNagumo MathlibExt.Biology.Dynamics.PlanarStability

/-! ### The rest state -/

/-- `(-3/2, -3/8)` is an equilibrium for `a = 6/5`, `b = 4/5`, `ε = 2/25`, `I = 0`
(computed from the definitions). -/
example : IsEquilibrium (6 / 5) (4 / 5) (2 / 25) 0 (-3 / 2) (-3 / 8) := by
  norm_num [IsEquilibrium, vField, wField]

/-- It is the only equilibrium (`0 < b ≤ 1`). -/
example (p : ℝ × ℝ) (hp : IsEquilibrium (6 / 5) (4 / 5) (2 / 25) 0 p.1 p.2) :
    p = (-3 / 2, -3 / 8) := by
  obtain ⟨q, -, hq⟩ := existsUnique_equilibrium (a := 6 / 5) (I := 0) (b := 4 / 5)
    (ε := 2 / 25) (by norm_num) (by norm_num) (by norm_num)
  rw [hq p hp, hq (-3 / 2, -3 / 8) (by norm_num [IsEquilibrium, vField, wField])]

/-- The rest state as a constant solution (non-vacuity of `IsSolution`). -/
example : IsSolution (6 / 5) (4 / 5) (2 / 25) 0 (fun _ => -3 / 2) (fun _ => -3 / 8) := by
  intro t _
  constructor
  · convert hasDerivAt_const t (-3 / 2 : ℝ) using 1; norm_num [vField]
  · convert hasDerivAt_const t (-3 / 8 : ℝ) using 1; norm_num [wField]

/-! ### Linearization at the rest state -/

example : jacTrace (4 / 5) (2 / 25) (-3 / 2) = -657 / 500 := by norm_num [jacTrace]

example : jacDet (4 / 5) (2 / 25) (-3 / 2) = 4 / 25 := by norm_num [jacDet]

/-- The determinant formula agrees with the matrix determinant. -/
example : (jacobian (4 / 5) (2 / 25) (-3 / 2)).det = 4 / 25 := by
  rw [det_jacobian]; norm_num [jacDet]

/-- `τ < 0 < Δ` and `4Δ = 16/25 ≤ τ² = 431649/250000`: a stable node. -/
example : equilibriumType (4 / 5) (2 / 25) (-3 / 2) = .stableNode :=
  linearType_eq_stableNode_iff.2 ⟨by norm_num [jacDet], by norm_num [jacTrace],
    by norm_num [jacDet, jacTrace]⟩

/-- Linearly stable, via the parameter criterion `v*² = 9/4 > 1 - ε b = 117/125`. -/
example :
    IsLinearlyStable (jacTrace (4 / 5) (2 / 25) (-3 / 2)) (jacDet (4 / 5) (2 / 25) (-3 / 2)) :=
  (isLinearlyStable_iff_of_lt_one (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)

/-- The same criterion in Hurwitz form: the Jacobian at rest is `Matrix.IsHurwitz`. -/
example : (jacobian (4 / 5) (2 / 25) (-3 / 2)).IsHurwitz :=
  (isHurwitz_jacobian_iff_of_lt_one (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)

/-- Unstable probe: `b = 3/4`, `ε = 1`, `v = 0` has `v² = 0 < 1 - ε b = 1/4`, so the Jacobian has
an eigenvalue with positive real part. -/
example : ∃ μ ∈ spectrum ℂ ((jacobian (3 / 4) 1 0).map (algebraMap ℝ ℂ)), 0 < μ.re :=
  (exists_spectrum_jacobian_re_pos_iff_of_lt_one (by norm_num) (by norm_num) (by norm_num)).2
    (by norm_num)

/-- At rest (`v*² = 9/4 > 117/125`) no eigenvalue of the Jacobian has positive real part. -/
example : ¬ ∃ μ ∈ spectrum ℂ ((jacobian (4 / 5) (2 / 25) (-3 / 2)).map (algebraMap ℝ ℂ)),
    0 < μ.re := by
  rw [exists_spectrum_jacobian_re_pos_iff_of_lt_one (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Every eigenvalue of the Jacobian at rest has negative real part. -/
example (z : ℂ)
    (hz : ((jacobian (4 / 5) (2 / 25) (-3 / 2)).map (fun r : ℝ => (r : ℂ)) -
      z • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0) : z.re < 0 :=
  ((isCharRoot_iff_det _ _ _ z).2 hz).re_neg (by norm_num [jacTrace]) (by norm_num [jacDet])

/-- Boundary probe (purely imaginary eigenvalues): `b = 3/4`, `ε = 1`, `v = 1/2` gives
`v² = 1/4 = 1 - ε b`, a linear center; the eigenvalues `± i √(7/16)` are purely imaginary. -/
example : equilibriumType (3 / 4) 1 (1 / 2) = .center :=
  (equilibriumType_eq_center_iff_of_lt_one (by norm_num) (by norm_num) (by norm_num)).2
    (by norm_num)

example : jacTrace (3 / 4) 1 (1 / 2) = 0 ∧ jacDet (3 / 4) 1 (1 / 2) = 7 / 16 := by
  norm_num [jacTrace, jacDet]

/-- At that probe every eigenvalue of the Jacobian is purely imaginary and nonzero. -/
example {μ : ℂ} (hμ : μ ∈ spectrum ℂ ((jacobian (3 / 4) 1 (1 / 2)).map (algebraMap ℝ ℂ))) :
    μ.re = 0 ∧ μ.im ≠ 0 :=
  re_eq_zero_and_im_ne_zero_of_mem_spectrum_jacobian (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hμ

/-- Boundary probe (saddle; for `b > 0` only possible when `b > 1`): `b = 4`, `v = 0` has
`b (1 - v²) = 4 > 1`. -/
example : equilibriumType 4 1 0 = .saddle := (equilibriumType_eq_saddle_iff one_pos).2 (by norm_num)

/-- In a saddle some eigenvalue has positive real part. -/
example : IsLinearlyUnstable (jacTrace 4 1 0) (jacDet 4 1 0) :=
  isLinearlyUnstable_of_linearType
    (Or.inl ((equilibriumType_eq_saddle_iff one_pos).2 (by norm_num)))

/-! ### The trapping ellipse -/

theorem trapRadius_ex : trapRadius (6 / 5) (4 / 5) (2 / 25) 0 = 1475 / 8 := by
  rw [trapRadius, decayRate, min_eq_right (by norm_num)]
  norm_num [absorbConst]

/-- Rational points on the boundary `v² + w² / ε = 200` of the level-`200` ellipse
(`200 > trapRadius = 184.375`). -/
example : energy (2 / 25) (-40 / 3) (-4 / 3) = 200 ∧ energy (2 / 25) (40 / 3) (-4 / 3) = 200 ∧
    energy (2 / 25) (-40 / 3) (4 / 3) = 200 ∧ energy (2 / 25) (-80 / 9) (-28 / 9) = 200 ∧
    energy (2 / 25) 0 4 = 200 ∧ energy (2 / 25) 0 (-4) = 200 := by
  norm_num [energy]

/-- **Boundary check, computed from the definitions.** The flux `⟪∇energy, field⟫` is negative at
each of those boundary points: the field points into the ellipse. -/
example : energyFlux (6 / 5) (4 / 5) (2 / 25) 0 (-40 / 3) (-4 / 3) < 0 ∧
    energyFlux (6 / 5) (4 / 5) (2 / 25) 0 (40 / 3) (-4 / 3) < 0 ∧
    energyFlux (6 / 5) (4 / 5) (2 / 25) 0 (-40 / 3) (4 / 3) < 0 ∧
    energyFlux (6 / 5) (4 / 5) (2 / 25) 0 (-80 / 9) (-28 / 9) < 0 ∧
    energyFlux (6 / 5) (4 / 5) (2 / 25) 0 0 4 < 0 ∧
    energyFlux (6 / 5) (4 / 5) (2 / 25) 0 0 (-4) < 0 := by
  norm_num [energyFlux, vField, wField]

/-- The same, through the trapping theorem. -/
example {v w : ℝ} (h : energy (2 / 25) v w = 200) : energyFlux (6 / 5) (4 / 5) (2 / 25) 0 v w < 0 :=
  energyFlux_neg_of_energy_eq (by norm_num) (by norm_num) (by rw [trapRadius_ex]; norm_num) h

/-- Probe: the small ellipse `energy = 1` is not trapping; at `(1, 0)` the field points outward
(flux `4/3 > 0`). -/
example : energy (2 / 25) 1 0 = 1 ∧ 0 < energyFlux (6 / 5) (4 / 5) (2 / 25) 0 1 0 := by
  norm_num [energy, energyFlux, vField, wField]

/-- Forward invariance of the level-`200` ellipse for every solution starting inside it. -/
example {v w : ℝ → ℝ} (h : IsSolution (6 / 5) (4 / 5) (2 / 25) 0 v w)
    (h0 : energy (2 / 25) (v 0) (w 0) ≤ 200) {t : ℝ} (ht : 0 ≤ t) :
    energy (2 / 25) (v t) (w t) ≤ 200 :=
  h.energy_le (by norm_num) (by norm_num) (by rw [trapRadius_ex]; norm_num) h0 ht

/-! ### Single pulses from the rest state: definitions -/

/-- `δ = 1/2`: `vField 0 (-1) (-3/8) = -7/24 < 0`, the voltage falls after the pulse. -/
example : IsFallingAfterPulse 0 (-3 / 2) (-3 / 8) (1 / 2) := by
  norm_num [IsFallingAfterPulse, vField]

/-- `δ = 2`: `vField 0 (1/2) (-3/8) = 5/6 > 0`, the voltage rises after the pulse. -/
example : IsRisingAfterPulse 0 (-3 / 2) (-3 / 8) 2 := by norm_num [IsRisingAfterPulse, vField]

/-- `δ = 4` overshoots the excited branch: `vField 0 (5/2) (-3/8) = -7/3 < 0`. -/
example : IsFallingAfterPulse 0 (-3 / 2) (-3 / 8) 4 := by norm_num [IsFallingAfterPulse, vField]

/-- The closed form of the post-pulse field agrees with the definition at `δ = 2`. -/
example : vField 0 (-3 / 2 + 2) (-3 / 8) = 2 * (1 - (-3 / 2) ^ 2 - (-3 / 2) * 2 - 2 ^ 2 / 3) :=
  vField_pulse (by norm_num [vField]) 2

/-- The lower root `pulseRootLow (-3/2) = (9/2 - √(21/4))/2 ≈ 1.10` separates the two pulses:
`1/2 < pulseRootLow (-3/2) < 2 < pulseRootHigh (-3/2)`. -/
example : 1 / 2 < pulseRootLow (-3 / 2) ∧ pulseRootLow (-3 / 2) < 2 ∧
    2 < pulseRootHigh (-3 / 2) := by
  have h0 := Real.sqrt_nonneg (12 - 3 * (-3 / 2 : ℝ) ^ 2)
  have h1 : √(12 - 3 * (-3 / 2 : ℝ) ^ 2) < 7 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h2 : 1 / 2 < √(12 - 3 * (-3 / 2 : ℝ) ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  unfold pulseRootLow pulseRootHigh
  refine ⟨by linarith, by linarith, by linarith⟩

/-- At the endpoint `v = -2` of `stable_rest_pulse_drift` the two roots coincide, so the rising
window is empty there. -/
example : pulseRootLow (-2) = 3 ∧ pulseRootHigh (-2) = 3 := by
  norm_num [pulseRootLow, pulseRootHigh]

/-- The rising-window theorem applies to the rest state. -/
example : 0 < pulseRootLow (-3 / 2) ∧ IsFallingAfterPulse 0 (-3 / 2) (-3 / 8) (1 / 2) := by
  obtain ⟨-, hpos, -, hsub, -⟩ := stable_rest_rising_pulse_window (a := 6 / 5) (b := 4 / 5)
    (ε := 2 / 25) (I := 0) (v := -3 / 2) (w := -3 / 8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [IsEquilibrium, vField, wField])
    (by norm_num) (by norm_num)
  refine ⟨hpos, hsub _ (by norm_num) ?_⟩
  have h1 : √(12 - 3 * (-3 / 2 : ℝ) ^ 2) < 7 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold pulseRootLow
  linarith

/-! ### Single pulses from the rest state: full dynamics (`ε = 10⁻⁵`, `T = 2`) -/

theorem trapRadius_slow : trapRadius (6 / 5) (4 / 5) (1 / 100000) 0 = 1475000 := by
  rw [trapRadius, decayRate, min_eq_right (by norm_num)]
  norm_num [absorbConst]

/-- Along any solution starting at `(v₀, -3/8)` with `|v₀| ≤ 3`, the trapping ellipse gives
`|v + a - b w| ≤ 12194/10` for all `t ≥ 0`. -/
theorem drift_bound {v w : ℝ → ℝ} (h : IsSolution (6 / 5) (4 / 5) (1 / 100000) 0 v w)
    (hv0 : |v 0| ≤ 3) (hw0 : w 0 = -3 / 8) {t : ℝ} (ht : 0 ≤ t) :
    |v t + 6 / 5 - 4 / 5 * w t| ≤ 12194 / 10 := by
  have hE := h.energy_le_max (by norm_num) (by norm_num) ht
  have hmax : max (energy (1 / 100000) (v 0) (w 0)) (trapRadius (6 / 5) (4 / 5) (1 / 100000) 0 + 1)
      = 1475001 := by
    rw [trapRadius_slow, max_eq_right]
    · norm_num
    · have : v 0 ^ 2 ≤ 9 := by nlinarith [abs_le.1 hv0]
      rw [energy, hw0]; norm_num; linarith
  rw [hmax] at hE
  have hb := abs_le_of_energy_le (a := 6 / 5) (b := 4 / 5) (by norm_num) hE
  have hs1 : √(1475001 : ℝ) ≤ 1215 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs2 : √((1 / 100000 : ℝ) * 1475001) ≤ 4 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have : |(6 / 5 : ℝ)| = 6 / 5 := abs_of_pos (by norm_num)
  have : |(4 / 5 : ℝ)| = 4 / 5 := abs_of_pos (by norm_num)
  linarith

/-- **Falling pulse, full dynamics.** The solution started by the pulse `δ = 1/2` from rest
never exceeds `v = -1` on `[0, 2]`. -/
example : ∃ v w : ℝ → ℝ, IsSolution (6 / 5) (4 / 5) (1 / 100000) 0 v w ∧ v 0 = -3 / 2 + 1 / 2 ∧
    w 0 = -3 / 8 ∧ ∀ t ∈ Icc (0 : ℝ) 2, v t ≤ -1 := by
  obtain ⟨v, w, h, hv0, hw0⟩ := exists_isSolution (a := 6 / 5) (b := 4 / 5) (ε := 1 / 100000)
    (I := 0) (by norm_num) (by norm_num) (-3 / 2 + 1 / 2) (-3 / 8)
  have hsub := (single_pulse_response (by norm_num [IsEquilibrium, vField, wField]) h hv0 hw0
    (T := 2) (M := 12194 / 10) (by norm_num) fun s hs => drift_bound h (by rw [hv0]; norm_num) hw0
      hs.1).1
    (by norm_num)
  exact ⟨v, w, h, hv0, hw0, fun t ht => by have := hsub t ht; linarith⟩

/-- **Rising pulse, full dynamics.** The solution started by the pulse `δ = 2` from the same rest
state reaches `v = 3/2` (beyond the knee `v = 1` of the cubic nullcline)
within `[0, 2]`. -/
example : ∃ v w : ℝ → ℝ, IsSolution (6 / 5) (4 / 5) (1 / 100000) 0 v w ∧ v 0 = -3 / 2 + 2 ∧
    w 0 = -3 / 8 ∧ ∃ t ∈ Icc (0 : ℝ) 2, 3 / 2 ≤ v t := by
  obtain ⟨v, w, h, hv0, hw0⟩ := exists_isSolution (a := 6 / 5) (b := 4 / 5) (ε := 1 / 100000)
    (I := 0) (by norm_num) (by norm_num) (-3 / 2 + 2) (-3 / 8)
  have hsup := (single_pulse_response (by norm_num [IsEquilibrium, vField, wField]) h hv0 hw0
    (T := 2) (M := 12194 / 10) (by norm_num) fun s hs => drift_bound h (by rw [hv0]; norm_num) hw0
      hs.1).2
    (3 / 2) (3 / 4) (by norm_num) (fun u hu => by
      have h1 : 0 ≤ 3 / 2 - u := by linarith [hu.2]
      have h2 : 0 ≤ u ^ 2 + 3 / 2 * u - 3 / 4 := by nlinarith [hu.1]
      unfold vField
      nlinarith [mul_nonneg h1 h2]) (by norm_num) (by norm_num)
  exact ⟨v, w, h, hv0, hw0, hsup⟩

/-! ### Return to rest -/

/-- From the definition, `restFactor (-3/2) (9/4) = 7/16 > 0`: at the classical rest state the
band `restFactor > 0` is nonempty, so `eq_rest_of_periodic` does not apply everywhere there. -/
example : restFactor (-3 / 2) (9 / 4) = 7 / 16 := by norm_num [restFactor]

/-- The displacement `9/4` lies in the rising-pulse window `(pulseRootLow, pulseRootHigh)`. -/
example : pulseRootLow (-3 / 2) < 9 / 4 ∧ (9 / 4 : ℝ) < pulseRootHigh (-3 / 2) :=
  (restFactor_pos_iff (by norm_num)).1 (by norm_num [restFactor])

/-- **Probe: the basin hypothesis is needed.** At `(v, w) = (3/4, -3/8)`, displacement `9/4`
from rest, the flux of `restEnergy` computed from the definitions is `567/128 > 0`: the shifted
energy increases there. -/
example : restFlux (6 / 5) (4 / 5) (2 / 25) 0 (-3 / 2) (-3 / 8) (3 / 4) (-3 / 8) = 567 / 128 := by
  norm_num [restFlux, vField, wField]

/-- The closed form `restFlux_eq` agrees with the definition at that point. -/
example : restFlux (6 / 5) (4 / 5) (2 / 25) 0 (-3 / 2) (-3 / 8) (3 / 4) (-3 / 8) =
    2 * ((9 / 4) ^ 2 * (7 / 16) - 4 / 5 * 0 ^ 2) := by
  norm_num [restFlux, vField, wField]

theorem abs_rest : |(-3 / 2 : ℝ)| = 3 / 2 := by rw [abs_of_neg (by norm_num)]; norm_num

/-- The basin condition `|v*| ρ < v*² - 1` holds at `ρ = 2/3` (`1 < 5/4`) and fails at `ρ = 5/6`
(equality). -/
example : |(-3 / 2 : ℝ)| * (2 / 3) < (-3 / 2) ^ 2 - 1 ∧
    ¬ |(-3 / 2 : ℝ)| * (5 / 6) < (-3 / 2) ^ 2 - 1 := by
  rw [abs_rest]; norm_num

/-- **Return to rest after the falling pulse.** The solution started by the pulse `δ = 1/2` from
the rest state (`restEnergy = 1/4 ≤ (2/3)²`) converges to the rest state, with
`restEnergy(t) ≤ e^{-16 t / 125} / 4`. -/
example : ∃ v w : ℝ → ℝ, IsSolution (6 / 5) (4 / 5) (2 / 25) 0 v w ∧ v 0 = -3 / 2 + 1 / 2 ∧
    w 0 = -3 / 8 ∧ Tendsto (fun t => (v t, w t)) atTop (𝓝 (-3 / 2, -3 / 8)) ∧
    ∀ t, 0 ≤ t → restEnergy (2 / 25) (-3 / 2) (-3 / 8) (v t) (w t) ≤
      exp (-(16 / 125) * t) * (1 / 4) := by
  obtain ⟨v, w, h, hv0, hw0⟩ := exists_isSolution (a := 6 / 5) (b := 4 / 5) (ε := 2 / 25)
    (I := 0) (by norm_num) (by norm_num) (-3 / 2 + 1 / 2) (-3 / 8)
  have hrest : IsEquilibrium (6 / 5) (4 / 5) (2 / 25) 0 (-3 / 2) (-3 / 8) := by
    norm_num [IsEquilibrium, vField, wField]
  have hE0 : restEnergy (2 / 25) (-3 / 2) (-3 / 8) (v 0) (w 0) = 1 / 4 := by
    rw [hv0, hw0]; norm_num [restEnergy, energy]
  have hρv : |(-3 / 2 : ℝ)| * (2 / 3) < (-3 / 2) ^ 2 - 1 := by rw [abs_rest]; norm_num
  have h0 : restEnergy (2 / 25) (-3 / 2) (-3 / 8) (v 0) (w 0) ≤ (2 / 3) ^ 2 := by
    rw [hE0]; norm_num
  refine ⟨v, w, h, hv0, hw0,
    h.tendsto_rest_of_basin hrest (by norm_num) (by norm_num) (by norm_num) hρv h0, fun t ht => ?_⟩
  have := h.restEnergy_le_exp_of_basin hrest (by norm_num) (by norm_num) (by norm_num) hρv h0 ht
  have hk : min ((-3 / 2 : ℝ) ^ 2 - 1 - |(-3 / 2 : ℝ)| * (2 / 3)) (4 / 5 * (2 / 25)) = 8 / 125 := by
    rw [abs_rest, min_eq_right (by norm_num)]; norm_num
  rw [hk, hE0] at this
  convert this using 3
  norm_num

/-! ### Global return to rest and no periodic orbits: `a = 6`, `b = 1/2`, `ε = 1`, `I = 0`

The rest state is `(-3, 6)`, with `v*² = 9 > 4`. -/

example : IsEquilibrium 6 (1 / 2) 1 0 (-3) 6 := by norm_num [IsEquilibrium, vField, wField]

/-- The bound `restFactor_le` is attained, from the definition:
`restFactor (-3) (9/2) = -5/4 = 1 - 9/4`. -/
example : restFactor (-3) (9 / 2) = -5 / 4 := by norm_num [restFactor]

/-- The solution from `(10, -10)` converges to the rest state. -/
example : ∃ v w : ℝ → ℝ, IsSolution 6 (1 / 2) 1 0 v w ∧ v 0 = 10 ∧ w 0 = -10 ∧
    Tendsto (fun t => (v t, w t)) atTop (𝓝 (-3, 6)) := by
  obtain ⟨v, w, h, hv0, hw0⟩ := exists_isSolution (a := 6) (b := 1 / 2) (ε := 1) (I := 0)
    (by norm_num) (by norm_num) 10 (-10)
  exact ⟨v, w, h, hv0, hw0, h.tendsto_rest_of_four_lt_sq
    (by norm_num [IsEquilibrium, vField, wField]) (by norm_num) (by norm_num) (by norm_num)⟩

/-- Every periodic solution is the rest state. -/
example {v w : ℝ → ℝ} (h : IsSolution 6 (1 / 2) 1 0 v w) {T : ℝ} (hT : 0 < T)
    (hvT : ∀ t, 0 ≤ t → v (t + T) = v t) (hwT : ∀ t, 0 ≤ t → w (t + T) = w t) {t : ℝ}
    (ht : 0 ≤ t) : v t = -3 ∧ w t = 6 :=
  h.eq_rest_of_periodic_of_four_le_sq (by norm_num [IsEquilibrium, vField, wField]) (by norm_num)
    (by norm_num) (by norm_num) hT hvT hwT ht

/-! ### Boundary `v*² = 4`: `a = 5/2`, `b = 3/4`, `ε = 1`, `I = 0`, rest state `(-2, 2/3)` -/

example : IsEquilibrium (5 / 2) (3 / 4) 1 0 (-2) (2 / 3) := by
  norm_num [IsEquilibrium, vField, wField]

/-- From the definition, `restFactor (-2) x = -(x - 3)² / 3 ≤ 0`, with equality at `x = 3`: the
band `restFactor > 0` is empty, and the global rate `min (v*²/4 - 1) (b ε)` is `0`. -/
example : restFactor (-2) 3 = 0 := by norm_num [restFactor]

example (x : ℝ) : restFactor (-2) x = -(x - 3) ^ 2 / 3 := by unfold restFactor; ring

example : min ((-2 : ℝ) ^ 2 / 4 - 1) (3 / 4 * 1) = 0 := by norm_num

/-- The rest state is a periodic solution of every period (the periodicity hypotheses are
satisfiable). -/
example : IsSolution (5 / 2) (3 / 4) 1 0 (fun _ => -2) (fun _ => 2 / 3) := by
  intro t _
  constructor
  · convert hasDerivAt_const t (-2 : ℝ) using 1; norm_num [vField]
  · convert hasDerivAt_const t (2 / 3 : ℝ) using 1; norm_num [wField]

/-- Periodic orbits are still excluded at `v*² = 4`. -/
example {v w : ℝ → ℝ} (h : IsSolution (5 / 2) (3 / 4) 1 0 v w) {T : ℝ} (hT : 0 < T)
    (hvT : ∀ t, 0 ≤ t → v (t + T) = v t) (hwT : ∀ t, 0 ≤ t → w (t + T) = w t) {t : ℝ}
    (ht : 0 ≤ t) : v t = -2 ∧ w t = 2 / 3 :=
  h.eq_rest_of_periodic_of_four_le_sq (by norm_num [IsEquilibrium, vField, wField]) (by norm_num)
    (by norm_num) (by norm_num) hT hvT hwT ht

/-! ### Endpoints of the window `restFactor > 0` -/

/-- At `v* = -1` the window is `(0, 3)`: its lower end is `0`, so all its amplitudes are positive
(`pulseRootLow_nonneg`), although `pulseRootLow_pos` needs `v* < -1`. -/
example : pulseRootLow (-1) = 0 ∧ pulseRootHigh (-1) = 3 := by
  have h : √(12 - 3 * (-1 : ℝ) ^ 2) = 3 := by
    rw [show (12 : ℝ) - 3 * (-1) ^ 2 = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold pulseRootLow pulseRootHigh
  rw [h]
  norm_num

/-- At `v* = 2` the two roots coincide, so the window is empty. -/
example : pulseRootLow 2 = -3 ∧ pulseRootHigh 2 = -3 := by
  norm_num [pulseRootLow, pulseRootHigh]

/-- At `v* = 0` the window contains the nonpositive displacement `-1`, where `restFactor = 2/3`
but the voltage field `x · restFactor` is `-2/3`. -/
example : pulseRootLow 0 < -1 ∧ (-1 : ℝ) < pulseRootHigh 0 ∧ restFactor 0 (-1) = 2 / 3 :=
  ⟨(restFactor_pos_iff (by norm_num)).1 (by norm_num [restFactor]) |>.1,
    (restFactor_pos_iff (by norm_num)).1 (by norm_num [restFactor]) |>.2,
    by norm_num [restFactor]⟩

/-- At the classical rest state a nonconstant periodic solution would have to visit the
rising-pulse window. -/
example {v w : ℝ → ℝ} (h : IsSolution (6 / 5) (4 / 5) (2 / 25) 0 v w) {T : ℝ} (hT : 0 < T)
    (hvT : ∀ t, 0 ≤ t → v (t + T) = v t) (hwT : ∀ t, 0 ≤ t → w (t + T) = w t)
    (hne : ∃ t₀, 0 ≤ t₀ ∧ (v t₀ ≠ -3 / 2 ∨ w t₀ ≠ -3 / 8)) :
    ∃ t, 0 ≤ t ∧ pulseRootLow (-3 / 2) < v t + 3 / 2 ∧ v t + 3 / 2 < pulseRootHigh (-3 / 2) := by
  obtain ⟨t, ht, h1, h2⟩ := h.exists_mem_pulse_window_of_periodic
    (by norm_num [IsEquilibrium, vField, wField]) (by norm_num) (by norm_num) (by norm_num) hT hvT
    hwT hne
  exact ⟨t, ht, by linarith, by linarith⟩

end MathlibExtTest.Biology.Biophysics.FitzHughNagumo
