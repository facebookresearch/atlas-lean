/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.FitzHughNagumo

/-! Tests for the FitzHugh–Nagumo model with the concrete parameters `a = 6/5`, `b = 4/5`, `I = 0`
(FitzHugh's `b = 0.8`; `a` chosen so that the rest state is rational): the rest state
`(v*, w*) = (-3/2, -3/8)` and its uniqueness, its linearization type, the trapping ellipse checked
pointwise on its boundary from the definitions (and a non-trapping small ellipse), boundary probes
of the classification (center, saddle), and sub- vs super-threshold pulses, both by the
definitions and through the full dynamics (`single_pulse_response` along solutions given by
`exists_isSolution`, with `ε = 10⁻⁵`). -/

open Real Set

namespace MathlibExtTest.Biology.Biophysics.FitzHughNagumo

open MathlibExt.Biology.Biophysics.FitzHughNagumo

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

/-- Every eigenvalue of the Jacobian at rest has negative real part. -/
example (z : ℂ)
    (hz : ((jacobian (4 / 5) (2 / 25) (-3 / 2)).map (fun r : ℝ => (r : ℂ)) -
      z • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0) : z.re < 0 :=
  ((isCharRoot_iff_det _ _ _ z).2 hz).re_neg (by norm_num [jacTrace]) (by norm_num [jacDet])

/-- Boundary probe (Hopf point): `b = 3/4`, `ε = 1`, `v = 1/2` gives `v² = 1/4 = 1 - ε b`, a
linear center; the eigenvalues `± i √(7/16)` are purely imaginary. -/
example : equilibriumType (3 / 4) 1 (1 / 2) = .center :=
  (equilibriumType_eq_center_iff_of_lt_one (by norm_num) (by norm_num) (by norm_num)).2
    (by norm_num)

example : jacTrace (3 / 4) 1 (1 / 2) = 0 ∧ jacDet (3 / 4) 1 (1 / 2) = 7 / 16 := by
  norm_num [jacTrace, jacDet]

/-- Boundary probe (saddle, only possible for `b > 1`): `b = 4`, `v = 0` has
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

/-- `δ = 1/2`: `vField 0 (-1) (-3/8) = -7/24 < 0`, sub-threshold. -/
example : IsSubThreshold 0 (-3 / 2) (-3 / 8) (1 / 2) := by norm_num [IsSubThreshold, vField]

/-- `δ = 2`: `vField 0 (1/2) (-3/8) = 5/6 > 0`, super-threshold. -/
example : IsSuperThreshold 0 (-3 / 2) (-3 / 8) 2 := by norm_num [IsSuperThreshold, vField]

/-- `δ = 4` overshoots the excited branch: `vField 0 (5/2) (-3/8) = -7/3 < 0`. -/
example : IsSubThreshold 0 (-3 / 2) (-3 / 8) 4 := by norm_num [IsSubThreshold, vField]

/-- The closed form of the post-pulse field agrees with the definition at `δ = 2`. -/
example : vField 0 (-3 / 2 + 2) (-3 / 8) = 2 * (1 - (-3 / 2) ^ 2 - (-3 / 2) * 2 - 2 ^ 2 / 3) :=
  vField_pulse (by norm_num [vField]) 2

/-- The firing threshold `thresholdLow (-3/2) = (9/2 - √(21/4))/2 ≈ 1.10` separates the two
pulses: `1/2 < thresholdLow (-3/2) < 2 < thresholdHigh (-3/2)`. -/
example : 1 / 2 < thresholdLow (-3 / 2) ∧ thresholdLow (-3 / 2) < 2 ∧
    2 < thresholdHigh (-3 / 2) := by
  have h0 := Real.sqrt_nonneg (12 - 3 * (-3 / 2 : ℝ) ^ 2)
  have h1 : √(12 - 3 * (-3 / 2 : ℝ) ^ 2) < 7 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h2 : 1 / 2 < √(12 - 3 * (-3 / 2 : ℝ) ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  unfold thresholdLow thresholdHigh
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The excitable-rest theorem applies to the rest state. -/
example : 0 < thresholdLow (-3 / 2) ∧ IsSubThreshold 0 (-3 / 2) (-3 / 8) (1 / 2) := by
  obtain ⟨-, hpos, hsub, -⟩ := excitable_rest (a := 6 / 5) (b := 4 / 5) (ε := 2 / 25) (I := 0)
    (v := -3 / 2) (w := -3 / 8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [IsEquilibrium, vField, wField])
    (by norm_num) (by norm_num)
  refine ⟨hpos, hsub _ (by norm_num) ?_⟩
  have h1 : √(12 - 3 * (-3 / 2 : ℝ) ^ 2) < 7 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold thresholdLow
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

/-- **Sub-threshold pulse, full dynamics.** The solution started by the pulse `δ = 1/2` from rest
never exceeds `v = -1` on `[0, 2]`. -/
example : ∃ v w : ℝ → ℝ, IsSolution (6 / 5) (4 / 5) (1 / 100000) 0 v w ∧ v 0 = -3 / 2 + 1 / 2 ∧
    w 0 = -3 / 8 ∧ ∀ t ∈ Icc (0 : ℝ) 2, v t ≤ -1 := by
  obtain ⟨v, w, h, hv0, hw0⟩ := exists_isSolution (a := 6 / 5) (b := 4 / 5) (ε := 1 / 100000)
    (I := 0) (by norm_num) (by norm_num) (-3 / 2 + 1 / 2) (-3 / 8)
  have hsub := (single_pulse_response (by norm_num [IsEquilibrium, vField, wField]) h hv0 hw0
    (T := 2) (M := 12194 / 10) fun s hs => drift_bound h (by rw [hv0]; norm_num) hw0 hs.1).1
    (by norm_num)
  exact ⟨v, w, h, hv0, hw0, fun t ht => by have := hsub t ht; linarith⟩

/-- **Super-threshold pulse, full dynamics.** The solution started by the pulse `δ = 2` from the
same rest state fires: it reaches `v = 3/2` (beyond the knee `v = 1` of the cubic nullcline)
within `[0, 2]`. -/
example : ∃ v w : ℝ → ℝ, IsSolution (6 / 5) (4 / 5) (1 / 100000) 0 v w ∧ v 0 = -3 / 2 + 2 ∧
    w 0 = -3 / 8 ∧ ∃ t ∈ Icc (0 : ℝ) 2, 3 / 2 ≤ v t := by
  obtain ⟨v, w, h, hv0, hw0⟩ := exists_isSolution (a := 6 / 5) (b := 4 / 5) (ε := 1 / 100000)
    (I := 0) (by norm_num) (by norm_num) (-3 / 2 + 2) (-3 / 8)
  have hsup := (single_pulse_response (by norm_num [IsEquilibrium, vField, wField]) h hv0 hw0
    (T := 2) (M := 12194 / 10) fun s hs => drift_bound h (by rw [hv0]; norm_num) hw0 hs.1).2
    (3 / 2) (3 / 4) (by norm_num) (fun u hu => by
      have h1 : 0 ≤ 3 / 2 - u := by linarith [hu.2]
      have h2 : 0 ≤ u ^ 2 + 3 / 2 * u - 3 / 4 := by nlinarith [hu.1]
      unfold vField
      nlinarith [mul_nonneg h1 h2]) (by norm_num) (by norm_num)
  exact ⟨v, w, h, hv0, hw0, hsup⟩

end MathlibExtTest.Biology.Biophysics.FitzHughNagumo
