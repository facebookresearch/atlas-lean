/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.EntryPorts

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Mechanics.EntryPorts`

SI units: `ρ0 = 1.225 kg/m³`, `H = 7000 m`, `β = 500 kg/m²`, `γ = π / 6` (`sin γ = 1 / 2`), a
declared band entered at `he = 40000 m` with `ve = 3000 m/s`; so `K = 17.15`.

* at `30000 m`, below the entry altitude, the density is positive and the speed lies strictly
  between `0` and the entry speed;
* the infinite-entry profile, which drops the `exp (-he / H)` term, misses the entry speed at
  the entry altitude.

Heat load and radiator, with an example Sutton-Graves correlation (`kSG = 1.7415e-4 kg^(1/2)/m`
for air, example validity box `ρ ≤ 0.01 kg/m³`, `rn ≥ 1 m`, `v ≤ 3000 m/s`, chosen for these
tests and not a published applicability range):

* the box is nonempty, and at its corner the flux is nonnegative and within the pointwise bound;
* the constant corner history over `10 s`, whose constant flux is interval integrable, has heat
  load `4702050 J/m²`, between `0` and the bound, which it attains;
* zero density gives zero heat load; outside the box (`v = 4000 m/s`) the correlation does not
  apply and its formula exceeds the in-box bound;
* along the profile above, the descending altitude history `40000 - 1250 t` on `[0, 4] s` stays
  in the band `[35000, 40000]` and in the box and has a continuous flux, so the band bound
  applies;
* a radiator with `ε = 0.8`, `σ = 5.670374419e-8 W/(m² K⁴)` and surroundings at `200 K` has a
  nonnegative equilibrium for `qabs = 100 W/m²`, and `300 K` is its only one for
  `qabs = 0.8 σ (300⁴ - 200⁴)`.

Peak deceleration along the profile above, where `hstar = 7000 log 34.3 ≈ 24.7 km`:

* the deceleration is positive; its derivative vanishes at `hstar` and not at `7000 log 17.15`,
  the candidate without the factor `2`;
* it increases with altitude below `hstar` and decreases above it;
* on `[0, 40000]` the interior `hstar` is selected, on `[35000, 40000]` the lower endpoint, and
  with entry at `20000 m` on `[10000, 20000]` the entry altitude; each selection maximizes the
  deceleration on its band, and the ground altitude of `[0, 40000]` stays strictly below it;
* with `β = 20000 kg/m²` the stationary point lies below the ground and is not reached in the
  band `[0, 40000]`.
-/

@[expose] public section

namespace PhyslibExtTest.Mechanics.EntryPorts

open _root_.EntryPorts

-- Nonzero density and descent: at `30000 m`, below the entry altitude, the density is positive
-- and the speed lies strictly between `0` and the entry speed (about `2.51 km/s`).
example :
    0 < exponentialDensity 1.225 7000 30000 ∧
      0 < ballisticVelocity 1.225 7000 500 (Real.pi / 6) 40000 3000 30000 ∧
      ballisticVelocity 1.225 7000 500 (Real.pi / 6) 40000 3000 30000 < 3000 := by
  have hsinpos : 0 < Real.sin (Real.pi / 6) := by rw [Real.sin_pi_div_six]; norm_num
  have hK : 0 < ballisticK 1.225 7000 500 (Real.pi / 6) :=
    ballisticK_pos (by norm_num) (by norm_num) (by norm_num) hsinpos
  refine ⟨?_, ?_, ?_⟩
  · unfold exponentialDensity
    exact mul_pos (by norm_num) (Real.exp_pos _)
  · exact ballisticVelocity_pos (by norm_num) _ _ _ _ _ _
  · have harg : (-40000 : ℝ) / 7000 < -30000 / 7000 := by norm_num
    have hexp : Real.exp (-40000 / 7000) < Real.exp (-30000 / 7000) :=
      Real.exp_lt_exp.mpr harg
    have hsub : Real.exp (-40000 / 7000) - Real.exp (-30000 / 7000) < 0 :=
      sub_neg.mpr hexp
    have hE : ballisticK 1.225 7000 500 (Real.pi / 6) *
        (Real.exp (-40000 / 7000) - Real.exp (-30000 / 7000)) < 0 :=
      mul_neg_of_pos_of_neg hK hsub
    have hlt : Real.exp (ballisticK 1.225 7000 500 (Real.pi / 6) *
        (Real.exp (-40000 / 7000) - Real.exp (-30000 / 7000))) < 1 :=
      Real.exp_lt_one_iff.mpr hE
    unfold ballisticVelocity
    calc 3000 * Real.exp (ballisticK 1.225 7000 500 (Real.pi / 6) *
          (Real.exp (-40000 / 7000) - Real.exp (-30000 / 7000)))
        < 3000 * 1 := mul_lt_mul_of_pos_left hlt (by norm_num)
      _ = 3000 := mul_one _

-- The infinite-entry profile misses the entry speed at the entry altitude (about `2.84 km/s`
-- instead of `3 km/s`).
example :
    3000 * Real.exp (ballisticK 1.225 7000 500 (Real.pi / 6) * -Real.exp (-40000 / 7000)) ≠
      3000 := by
  have hsinpos : 0 < Real.sin (Real.pi / 6) := by rw [Real.sin_pi_div_six]; norm_num
  exact omitted_entry_term_ne (by norm_num) (by norm_num) (by norm_num) hsinpos (by norm_num) _

/-- The example correlation of the fixtures. -/
noncomputable def exampleCorrelation : StagnationHeatingCorrelation where
  citation := "K. Sutton and R. A. Graves, NASA TR R-376, 1971"
  coefficient := 1.7415e-4
  maxDensity := 0.01
  minNoseRadius := 1
  maxSpeed := 3000
  coefficient_nonneg := by norm_num
  minNoseRadius_pos := by norm_num
  maxDensity_nonneg := by norm_num
  maxSpeed_nonneg := by norm_num

-- The validity box of the example correlation is nonempty.
example : ∃ ρ rn v : ℝ, exampleCorrelation.Applies ρ rn v :=
  exampleCorrelation.exists_applies

-- At the box corner the flux is nonnegative and at most the pointwise bound.
example : ∃ h : exampleCorrelation.Applies 0.01 1 3000,
    0 ≤ exampleCorrelation.heatFlux 0.01 1 3000 h ∧
      exampleCorrelation.heatFlux 0.01 1 3000 h ≤
        exampleCorrelation.coefficient *
          Real.sqrt (exampleCorrelation.maxDensity / exampleCorrelation.minNoseRadius) *
            exampleCorrelation.maxSpeed ^ 3 := by
  have h : exampleCorrelation.Applies 0.01 1 3000 :=
    ⟨⟨by norm_num, by norm_num [exampleCorrelation]⟩, by norm_num [exampleCorrelation],
      ⟨by norm_num, by norm_num [exampleCorrelation]⟩⟩
  exact ⟨h, exampleCorrelation.heatFlux_nonneg h, exampleCorrelation.heatFlux_le h⟩

-- The heat load of the constant corner history over `10 s` lies between `0` and the bound.
example (h : ∀ t ∈ Set.Icc (0 : ℝ) 10, exampleCorrelation.Applies 0.01 1 3000) :
    0 ≤ exampleCorrelation.heatLoad 10 (fun _ => 0.01) (fun _ => 1) (fun _ => 3000)
        (by norm_num) h ∧
      exampleCorrelation.heatLoad 10 (fun _ => 0.01) (fun _ => 1) (fun _ => 3000)
          (by norm_num) h ≤
        10 * exampleCorrelation.coefficient *
          Real.sqrt (exampleCorrelation.maxDensity / exampleCorrelation.minNoseRadius) *
            exampleCorrelation.maxSpeed ^ 3 :=
  ⟨exampleCorrelation.heatLoad_nonneg _ h intervalIntegrable_const,
    exampleCorrelation.heatLoad_le _ h intervalIntegrable_const⟩


-- Nonzero flux and positive horizon: the constant history at the box corner
-- `ρ = 0.01 kg / m ^ 3`, `rn = 1 m`, `v = 3000 m / s` stays in the example box over
-- `tf = 10 s`. Its heat flux is `1.7415e-4 * 0.1 * 3000 ^ 3 = 470205 W / m ^ 2` and its heat
-- load is `4702050 J / m ^ 2`, equal to the bound `tf * kSG * sqrt (ρmax / rmin) * vmax ^ 3`:
-- the bound is attained.
example :
    ∃ h : ∀ t ∈ Set.Icc (0 : ℝ) 10, exampleCorrelation.Applies 0.01 1 3000,
      exampleCorrelation.heatLoad 10 (fun _ => 0.01) (fun _ => 1) (fun _ => 3000)
          (by norm_num) h = 4702050 ∧
        10 * exampleCorrelation.coefficient * Real.sqrt (exampleCorrelation.maxDensity /
          exampleCorrelation.minNoseRadius) * exampleCorrelation.maxSpeed ^ 3 = 4702050 := by
  have hs : Real.sqrt ((0.01 : ℝ) / 1) = 0.1 := by
    rw [show (0.01 : ℝ) / 1 = 0.1 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨fun _ _ => ⟨⟨by norm_num, by norm_num [exampleCorrelation]⟩,
    by norm_num [exampleCorrelation], ⟨by norm_num, by norm_num [exampleCorrelation]⟩⟩, ?_, ?_⟩
  · unfold StagnationHeatingCorrelation.heatLoad
    simp only [intervalIntegral.integral_const, smul_eq_mul, exampleCorrelation, hs]
    norm_num
  · simp only [exampleCorrelation, hs]
    norm_num

-- Vacuum: the zero-density history at `rn = 1 m`, `v = 3000 m / s` stays in the example
-- box over `10 s` and has zero heat load.
example :
    ∃ h : ∀ t ∈ Set.Icc (0 : ℝ) 10, exampleCorrelation.Applies 0 1 3000,
      exampleCorrelation.heatLoad 10 (fun _ => 0) (fun _ => 1) (fun _ => 3000)
          (by norm_num) h = 0 := by
  refine ⟨fun _ _ => ⟨⟨le_rfl, by norm_num [exampleCorrelation]⟩,
    by norm_num [exampleCorrelation], ⟨by norm_num, by norm_num [exampleCorrelation]⟩⟩, ?_⟩
  exact StagnationHeatingCorrelation.heatLoad_vacuum _ _ _ fun _ _ => rfl

-- Leaving the validity box: at `v = 4000 m / s > vmax` the example correlation does not apply,
-- and its formula there, `1.7415e-4 * sqrt (0.01 / 1) * 4000 ^ 3 = 1114560 W / m ^ 2`, exceeds the
-- in-box flux bound `470205 W / m ^ 2`, so no bound is claimed outside the box.
example :
    ¬ exampleCorrelation.Applies 0.01 1 4000 ∧
      exampleCorrelation.coefficient * Real.sqrt (exampleCorrelation.maxDensity /
          exampleCorrelation.minNoseRadius) * exampleCorrelation.maxSpeed ^ 3 <
        exampleCorrelation.coefficient * Real.sqrt (0.01 / 1) * 4000 ^ 3 := by
  have hs : Real.sqrt ((0.01 : ℝ) / 1) = 0.1 := by
    rw [show (0.01 : ℝ) / 1 = 0.1 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨?_, ?_⟩
  · rintro ⟨-, -, -, hv⟩
    norm_num [exampleCorrelation] at hv
  · simp only [exampleCorrelation, hs]
    norm_num

-- Radiator: emissivity `0.8`, `σ = 5.670374419e-8 W / (m ^ 2 K ^ 4)`, surroundings at `200 K`
-- and absorbed flux `0.8 * σ * (300 ^ 4 - 200 ^ 4) ≈ 294.9 W / m ^ 2`: `300 K` is the only
-- nonnegative equilibrium.
example (T : ℝ) (hT : 0 ≤ T) :
    0.8 * 5.670374419e-8 * T ^ 4 =
        0.8 * 5.670374419e-8 * (300 ^ 4 - 200 ^ 4) + 0.8 * 5.670374419e-8 * 200 ^ 4 ↔
      T = 300 := by
  constructor
  · intro h
    exact radiator_equilibrium_unique (by norm_num) (by norm_num) (by norm_num) (by norm_num) hT
      (by norm_num) h (by norm_num)
  · rintro rfl
    norm_num

-- Along the profile of the first tests, the descending altitude history `40000 - 1250 t` on
-- `[0, 4] s` stays in the band `[35000, 40000]` and in the example box, so the band bound applies;
-- `ρ(35000) = 1.225 e⁻⁵ ≤ 0.01` follows from `(17 / 16) ^ 80 ≤ e⁵`.
example : ∃ hbox : ∀ t ∈ Set.Icc (0 : ℝ) 4, exampleCorrelation.Applies
      (exponentialDensity 1.225 7000 (40000 - 1250 * t)) 1
      (ballisticVelocity 1.225 7000 500 (Real.pi / 6) 40000 3000 (40000 - 1250 * t)),
    exampleCorrelation.heatLoad 4 (fun t => exponentialDensity 1.225 7000 (40000 - 1250 * t))
        (fun _ => 1)
        (fun t => ballisticVelocity 1.225 7000 500 (Real.pi / 6) 40000 3000 (40000 - 1250 * t))
        (by norm_num) hbox ≤
      4 * exampleCorrelation.coefficient *
        Real.sqrt (exponentialDensity 1.225 7000 35000 / exampleCorrelation.minNoseRadius) *
          3000 ^ 3 := by
  have hsin : 0 < Real.sin (Real.pi / 6) := by rw [Real.sin_pi_div_six]; norm_num
  have hband : ∀ t ∈ Set.Icc (0 : ℝ) 4, 40000 - 1250 * t ∈ Set.Icc (35000 : ℝ) 40000 := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hexp : (122.5 : ℝ) < Real.exp 5 := by
    have h1 : (17 / 16 : ℝ) ≤ Real.exp (1 / 16) := by
      have := Real.add_one_le_exp (1 / 16 : ℝ)
      norm_num at this
      exact this
    have h2 : Real.exp 5 = Real.exp (1 / 16) ^ 80 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h2]
    exact lt_of_lt_of_le (by norm_num) (pow_le_pow_left₀ (by norm_num) h1 80)
  have hρ35 : exponentialDensity 1.225 7000 35000 ≤ 0.01 := by
    unfold exponentialDensity
    rw [show (-35000 : ℝ) / 7000 = -5 by norm_num, Real.exp_neg]
    rw [mul_inv_le_iff₀ (Real.exp_pos 5)]
    linarith
  have hmono := (ballisticVelocity_strictMono (ρ0 := 1.225) (H := 7000) (β := 500)
    (γ := Real.pi / 6) (ve := 3000) (by norm_num) (by norm_num) (by norm_num) hsin
    (by norm_num) 40000).monotone
  have hbox : ∀ t ∈ Set.Icc (0 : ℝ) 4, exampleCorrelation.Applies
      (exponentialDensity 1.225 7000 (40000 - 1250 * t)) 1
      (ballisticVelocity 1.225 7000 500 (Real.pi / 6) 40000 3000 (40000 - 1250 * t)) := by
    intro t ht
    have hb := hband t ht
    have hρle : exponentialDensity 1.225 7000 (40000 - 1250 * t) ≤
        exponentialDensity 1.225 7000 35000 := by
      unfold exponentialDensity
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ (by norm_num)
      linarith [hb.1]
    have hvle := hmono hb.2
    rw [ballisticVelocity_entry] at hvle
    refine ⟨⟨?_, ?_⟩, by norm_num [exampleCorrelation], ⟨?_, ?_⟩⟩
    · unfold exponentialDensity
      exact (mul_pos (by norm_num) (Real.exp_pos _)).le
    · simpa [exampleCorrelation] using hρle.trans hρ35
    · exact (ballisticVelocity_pos (by norm_num) _ _ _ _ _ _).le
    · simpa [exampleCorrelation] using hvle
  have hint : IntervalIntegrable (fun t => exampleCorrelation.coefficient *
      Real.sqrt (exponentialDensity 1.225 7000 (40000 - 1250 * t) / 1) *
        ballisticVelocity 1.225 7000 500 (Real.pi / 6) 40000 3000 (40000 - 1250 * t) ^ 3)
      MeasureTheory.volume 0 4 := by
    refine Continuous.intervalIntegrable ?_ _ _
    unfold exponentialDensity ballisticVelocity
    simp only [div_one]
    fun_prop
  exact ⟨hbox, StagnationHeatingCorrelation.heatLoad_le_of_band exampleCorrelation (by norm_num)
    (by norm_num) (by norm_num) hsin (by norm_num) (by norm_num) hband hbox hint⟩

-- The radiator of the last fixture has a nonnegative equilibrium for an absorbed flux of
-- `100 W/m²` with surroundings at `200 K`.
example : ∃ T : ℝ, 0 ≤ T ∧
    0.8 * 5.670374419e-8 * T ^ 4 = 100 + 0.8 * 5.670374419e-8 * 200 ^ 4 :=
  radiator_equilibrium_exists (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- `20000 < hstar < 35000` for the profile of these tests: `hstar = 7000 log 34.3`, with
`exp (20 / 7) ≤ (7 / 6) ^ 20 < 34.3` and `34.3 < (3 / 2) ^ 10 ≤ exp 5`. -/
private lemma peakDecelerationAltitude_fixture_bounds :
    20000 < peakDecelerationAltitude 1.225 7000 500 (Real.pi / 6) ∧
      peakDecelerationAltitude 1.225 7000 500 (Real.pi / 6) < 35000 := by
  have hstar : peakDecelerationAltitude 1.225 7000 500 (Real.pi / 6) = 7000 * Real.log 34.3 := by
    unfold peakDecelerationAltitude ballisticK
    rw [Real.sin_pi_div_six]
    norm_num
  have hseventh : Real.exp (1 / 7) ≤ 7 / 6 := by
    have h := Real.add_one_le_exp (-(1 / 7) : ℝ)
    have hmul : Real.exp (-(1 / 7)) * Real.exp (1 / 7) = 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos (1 / 7 : ℝ)]
  have hhalf : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
  have hlo : 20 / 7 < Real.log 34.3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h20 : Real.exp (20 / 7) = Real.exp (1 / 7) ^ 20 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h20]
    exact lt_of_le_of_lt (pow_le_pow_left₀ (Real.exp_pos _).le hseventh 20) (by norm_num)
  have hhi : Real.log 34.3 < 5 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h5 : Real.exp 5 = Real.exp (1 / 2) ^ 10 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h5]
    exact lt_of_lt_of_le (by norm_num) (pow_le_pow_left₀ (by norm_num) hhalf 10)
  rw [hstar]
  exact ⟨by linarith, by linarith⟩

-- The deceleration at `30000 m` is positive.
example : 0 < ballisticDeceleration 1.225 7000 500 (Real.pi / 6) 40000 3000 30000 :=
  ballisticDeceleration_pos (by norm_num) (by norm_num) (by norm_num) _ _ _ _

-- The altitude derivative of the deceleration at any height.
example (h : ℝ) :
    HasDerivAt (ballisticDeceleration 1.225 7000 500 (Real.pi / 6) 40000 3000)
      (ballisticDeceleration 1.225 7000 500 (Real.pi / 6) 40000 3000 h *
        (2 * ballisticK 1.225 7000 500 (Real.pi / 6) * Real.exp (-h / 7000) - 1) / 7000) h :=
  hasDerivAt_ballisticDeceleration (by norm_num) _ _ _ _ _ h (by norm_num)
    (by rw [Real.sin_pi_div_six]; norm_num)

-- The derivative vanishes at `hstar`; dropping the factor `2` in `hstar` (`7000 log 17.15`)
-- gives an altitude where it does not.
example :
    deriv (ballisticDeceleration 1.225 7000 500 (Real.pi / 6) 40000 3000)
        (peakDecelerationAltitude 1.225 7000 500 (Real.pi / 6)) = 0 ∧
      deriv (ballisticDeceleration 1.225 7000 500 (Real.pi / 6) 40000 3000)
        (7000 * Real.log 17.15) ≠ 0 := by
  have hsin : 0 < Real.sin (Real.pi / 6) := by rw [Real.sin_pi_div_six]; norm_num
  have hiff := deriv_ballisticDeceleration_eq_zero_iff (ρ0 := 1.225) (H := 7000) (β := 500)
    (γ := Real.pi / 6) (ve := 3000) (by norm_num) (by norm_num) (by norm_num) hsin (by norm_num)
    40000
  refine ⟨(hiff _).2 rfl, fun h0 => ?_⟩
  have h1 := (hiff _).1 h0
  unfold peakDecelerationAltitude ballisticK at h1
  rw [Real.sin_pi_div_six] at h1
  have h2 : Real.log 17.15 = Real.log (2 * (1.225 * 7000 / (2 * 500 * (1 / 2)))) := by linarith
  have h3 : (17.15 : ℝ) = 2 * (1.225 * 7000 / (2 * 500 * (1 / 2))) :=
    Real.log_injOn_pos (by norm_num) (by norm_num) h2
  norm_num at h3

-- Below `hstar` the deceleration increases with altitude; above it, it decreases.
example :
    ballisticDeceleration 1.225 7000 500 (Real.pi / 6) 40000 3000 10000 <
        ballisticDeceleration 1.225 7000 500 (Real.pi / 6) 40000 3000 20000 ∧
      ballisticDeceleration 1.225 7000 500 (Real.pi / 6) 40000 3000 40000 <
        ballisticDeceleration 1.225 7000 500 (Real.pi / 6) 40000 3000 35000 := by
  have hsin : 0 < Real.sin (Real.pi / 6) := by rw [Real.sin_pi_div_six]; norm_num
  obtain ⟨hlo, hhi⟩ := peakDecelerationAltitude_fixture_bounds
  refine ⟨ballisticDeceleration_strictMonoOn (ρ0 := 1.225) (H := 7000) (β := 500)
    (γ := Real.pi / 6) (ve := 3000) (by norm_num) (by norm_num) (by norm_num) hsin (by norm_num)
    40000 (Set.mem_Iic.2 (by linarith)) (Set.mem_Iic.2 hlo.le) (by norm_num), ?_⟩
  exact ballisticDeceleration_strictAntiOn (ρ0 := 1.225) (H := 7000) (β := 500)
    (γ := Real.pi / 6) (ve := 3000) (by norm_num) (by norm_num) (by norm_num) hsin (by norm_num)
    40000 (Set.mem_Ici.2 hhi.le) (Set.mem_Ici.2 (by linarith)) (by norm_num)


-- Interior maximum: on the band `[0, 40000]` from the ground to the entry altitude, `hstar`
-- lies inside, is selected, and maximizes the deceleration (about `132 m / s ^ 2`).
example :
    peakDecelerationAltitude 1.225 7000 500 (Real.pi / 6) ∈ Set.Ioo 0 40000 ∧
      bandPeakAltitude 1.225 7000 500 (Real.pi / 6) 0 40000 =
        peakDecelerationAltitude 1.225 7000 500 (Real.pi / 6) ∧
      IsMaxOn (ballisticDeceleration 1.225 7000 500 (Real.pi / 6) 40000 3000) (Set.Icc 0 40000)
        (peakDecelerationAltitude 1.225 7000 500 (Real.pi / 6)) := by
  have hsin : 0 < Real.sin (Real.pi / 6) := by rw [Real.sin_pi_div_six]; norm_num
  have hstar : peakDecelerationAltitude 1.225 7000 500 (Real.pi / 6) = 7000 * Real.log 34.3 := by
    unfold peakDecelerationAltitude ballisticK
    rw [Real.sin_pi_div_six]
    norm_num
  have hlog : Real.log 34.3 < 40 / 7 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h1 : (17 / 7 : ℝ) ≤ Real.exp (10 / 7) := by linarith [Real.add_one_le_exp (10 / 7 : ℝ)]
    have h2 : Real.exp (40 / 7) = Real.exp (10 / 7) ^ 4 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h3 : (17 / 7 : ℝ) ^ 4 ≤ Real.exp (10 / 7) ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
    rw [h2]
    linarith [show (34.3 : ℝ) < (17 / 7) ^ 4 by norm_num]
  have hmem : peakDecelerationAltitude 1.225 7000 500 (Real.pi / 6) ∈ Set.Ioo 0 40000 := by
    rw [hstar]
    exact ⟨mul_pos (by norm_num) (Real.log_pos (by norm_num)), by linarith⟩
  have hsel := bandPeakAltitude_of_mem (he := 40000) (Set.Ioo_subset_Icc_self hmem)
  refine ⟨hmem, hsel, ?_⟩
  have hmax := (isMaxOn_bandPeakAltitude (ρ0 := 1.225) (H := 7000) (β := 500)
    (γ := Real.pi / 6) (ve := 3000) (by norm_num) (by norm_num) (by norm_num) hsin (by norm_num)
    (show (0 : ℝ) < 40000 by norm_num)).2
  rwa [hsel] at hmax

-- Endpoint maximum: on the band `[35000, 40000]` the candidate lies below the band, so the lower
-- endpoint is selected and maximizes the deceleration (about `66 m / s ^ 2` at `35 km` against
-- `36 m / s ^ 2` at entry).
example :
    peakDecelerationAltitude 1.225 7000 500 (Real.pi / 6) < 35000 ∧
      bandPeakAltitude 1.225 7000 500 (Real.pi / 6) 35000 40000 = 35000 ∧
      IsMaxOn (ballisticDeceleration 1.225 7000 500 (Real.pi / 6) 40000 3000)
        (Set.Icc 35000 40000) 35000 := by
  have hsin : 0 < Real.sin (Real.pi / 6) := by rw [Real.sin_pi_div_six]; norm_num
  have hstar : peakDecelerationAltitude 1.225 7000 500 (Real.pi / 6) = 7000 * Real.log 34.3 := by
    unfold peakDecelerationAltitude ballisticK
    rw [Real.sin_pi_div_six]
    norm_num
  have hlog : Real.log 34.3 < 5 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h1 : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
    have h2 : Real.exp 5 = Real.exp (1 / 2) ^ 10 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h3 : (3 / 2 : ℝ) ^ 10 ≤ Real.exp (1 / 2) ^ 10 := pow_le_pow_left₀ (by norm_num) h1 10
    rw [h2]
    linarith [show (34.3 : ℝ) < (3 / 2) ^ 10 by norm_num]
  have hlt : peakDecelerationAltitude 1.225 7000 500 (Real.pi / 6) < 35000 := by
    rw [hstar]
    linarith
  have hsel := bandPeakAltitude_of_lt (he := 40000) hlt
  refine ⟨hlt, hsel, ?_⟩
  have hmax := (isMaxOn_bandPeakAltitude (ρ0 := 1.225) (H := 7000) (β := 500)
    (γ := Real.pi / 6) (ve := 3000) (by norm_num) (by norm_num) (by norm_num) hsin (by norm_num)
    (show (35000 : ℝ) < 40000 by norm_num)).2
  rwa [hsel] at hmax

-- A stationary point below the ground is not an observed peak: for `β = 20000 kg / m ^ 2`,
-- `K = 0.42875` and `hstar = 7000 * log 0.8575 ≈ -1.08 km` lies below the band `[0, 40000]`. The
-- ground endpoint is selected, and every deceleration in the band stays strictly below the
-- stationary value.
example :
    peakDecelerationAltitude 1.225 7000 20000 (Real.pi / 6) < 0 ∧
      bandPeakAltitude 1.225 7000 20000 (Real.pi / 6) 0 40000 = 0 ∧
      ∀ h ∈ Set.Icc (0 : ℝ) 40000,
        ballisticDeceleration 1.225 7000 20000 (Real.pi / 6) 40000 3000 h <
          ballisticDeceleration 1.225 7000 20000 (Real.pi / 6) 40000 3000
            (peakDecelerationAltitude 1.225 7000 20000 (Real.pi / 6)) := by
  have hsin : 0 < Real.sin (Real.pi / 6) := by rw [Real.sin_pi_div_six]; norm_num
  have hstar :
      peakDecelerationAltitude 1.225 7000 20000 (Real.pi / 6) = 7000 * Real.log 0.8575 := by
    unfold peakDecelerationAltitude ballisticK
    rw [Real.sin_pi_div_six]
    norm_num
  have hneg : peakDecelerationAltitude 1.225 7000 20000 (Real.pi / 6) < 0 := by
    rw [hstar]
    exact mul_neg_of_pos_of_neg (by norm_num) (Real.log_neg (by norm_num) (by norm_num))
  refine ⟨hneg, bandPeakAltitude_of_lt hneg, fun h hh => ?_⟩
  exact ballisticDeceleration_lt_peak (ρ0 := 1.225) (H := 7000) (β := 20000) (γ := Real.pi / 6)
    (ve := 3000) (by norm_num) (by norm_num) (by norm_num) hsin (by norm_num) 40000
    (lt_of_lt_of_le hneg hh.1).ne'

-- Upper endpoint: with entry at `20000 m`, `hstar` lies above the band `[10000, 20000]`, so the
-- entry altitude is selected and maximizes the deceleration on the band.
example :
    20000 < peakDecelerationAltitude 1.225 7000 500 (Real.pi / 6) ∧
      bandPeakAltitude 1.225 7000 500 (Real.pi / 6) 10000 20000 = 20000 ∧
      IsMaxOn (ballisticDeceleration 1.225 7000 500 (Real.pi / 6) 20000 3000)
        (Set.Icc 10000 20000) 20000 := by
  have hsin : 0 < Real.sin (Real.pi / 6) := by rw [Real.sin_pi_div_six]; norm_num
  have hgt := peakDecelerationAltitude_fixture_bounds.1
  have hsel := bandPeakAltitude_of_gt (ρ0 := 1.225) (H := 7000) (β := 500) (γ := Real.pi / 6)
    (show (10000 : ℝ) < 20000 by norm_num) hgt
  refine ⟨hgt, hsel, ?_⟩
  have hmax := (isMaxOn_bandPeakAltitude (ρ0 := 1.225) (H := 7000) (β := 500)
    (γ := Real.pi / 6) (ve := 3000) (by norm_num) (by norm_num) (by norm_num) hsin (by norm_num)
    (show (10000 : ℝ) < 20000 by norm_num)).2
  rwa [hsel] at hmax

-- The selected altitude of `[0, 40000]` is the only maximizer: the ground altitude has a strictly
-- smaller deceleration.
example :
    ballisticDeceleration 1.225 7000 500 (Real.pi / 6) 40000 3000 0 <
      ballisticDeceleration 1.225 7000 500 (Real.pi / 6) 40000 3000
        (bandPeakAltitude 1.225 7000 500 (Real.pi / 6) 0 40000) := by
  have hsin : 0 < Real.sin (Real.pi / 6) := by rw [Real.sin_pi_div_six]; norm_num
  have hlo := peakDecelerationAltitude_fixture_bounds.1
  have hpos : 0 < bandPeakAltitude 1.225 7000 500 (Real.pi / 6) 0 40000 := by
    unfold bandPeakAltitude
    exact lt_of_lt_of_le (lt_min (by linarith) (by norm_num)) (le_max_right _ _)
  exact ballisticDeceleration_lt_bandPeakAltitude (by norm_num) (by norm_num) (by norm_num) hsin
    (by norm_num) (show (0 : ℝ) < 40000 by norm_num) ⟨le_rfl, by norm_num⟩ hpos.ne

end PhyslibExtTest.Mechanics.EntryPorts
