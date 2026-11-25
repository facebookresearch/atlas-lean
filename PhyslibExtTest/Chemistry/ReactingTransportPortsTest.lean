/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.ReactingTransportPorts
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Tests for `PhyslibExt.Chemistry.ReactingTransportPorts`

Reduced coordinates with dilution and cooling rates `a = h = 1`, heat-release factor `b = 2`,
Arrhenius constants `A = B = 1`, and inlet and coolant values `cin = Tin = Tc = 1`; from the
initial state `(c0, T0) = (1/2, 3/2)` the box is `0 ≤ c ≤ 1`, `1 ≤ T ≤ 2`.

* the box values, an interior initial state and a positive reaction term there;
* the physical path from that state exists for all forward time and stays in the box, and every
  forward solution from it stays in the box;
* the floor face points into the box; the extended rate equals the Arrhenius rate on the box,
  stays in `[0, A]` below it, and gives a continuous field;
* invalid inputs: zero inlet and coolant temperatures lose the positive floor and the continuity
  of the extended rate; an endothermic reaction leaves the box through the floor.
-/

@[expose] public section

namespace PhyslibExtTest.Chemistry.ReactingTransportPorts

open _root_.Chemistry.ReactingTransportPorts

/-- Nonzero reaction in the interior of the box: for `a = 1`, `b = 2`, `h = 1`, `A = 1`, `B = 1`,
`cin = 1`, `Tin = Tc = 1`, `c0 = 1/2`, `T0 = 3/2` the box is `0 ≤ c ≤ 1`, `1 ≤ T ≤ 2`, the
initial state is interior, and the reaction term `k(T0) c0` is positive. -/
lemma interiorReaction_fixture :
    concentrationCeiling (1 / 2) 1 = 1 ∧ temperatureFloor 1 1 1 1 (3 / 2) = 1 ∧
      temperatureCeiling 1 2 1 1 1 1 (3 / 2) 1 = 2 ∧ (1 / 2 : ℝ) ∈ Set.Ioo 0 1 ∧
      (3 / 2 : ℝ) ∈ Set.Ioo 1 2 ∧ 0 < arrheniusRateConstant 1 1 (3 / 2) * (1 / 2) := by
  refine ⟨by norm_num [concentrationCeiling], by norm_num [temperatureFloor],
    by norm_num [temperatureCeiling], by norm_num, by norm_num, ?_⟩
  unfold arrheniusRateConstant
  positivity

/-- The fixture path: from the interior state `(1/2, 3/2)` the physical path exists for all
forward time, stays in the box `[0, 1] × [1, 2]`, and starts with a positive reaction term. -/
lemma interiorReaction_path :
    ∃ c T : ℝ → ℝ, c 0 = 1 / 2 ∧ T 0 = 3 / 2 ∧
      (∀ t, 0 ≤ t →
        (c t ∈ Set.Icc 0 1 ∧ T t ∈ Set.Icc 1 2) ∧
        HasDerivAt c (concentrationRhs 1 1 (arrheniusRateConstant 1 1 (T t)) (c t)) t ∧
        HasDerivAt T (temperatureRhs 1 2 1 1 1 (arrheniusRateConstant 1 1 (T t)) (c t) (T t)) t) ∧
      0 < arrheniusRateConstant 1 1 (T 0) * c 0 := by
  obtain ⟨c, T, hc0, hT0, hsol⟩ := exists_arrhenius_path (a := 1) (b := 2) (h := 1) (A := 1)
    (B := 1) (cin := 1) (Tin := 1) (Tc := 1) (c0 := 1 / 2) (T0 := 3 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hcc, hfl, hce, -, -, -⟩ := interiorReaction_fixture
  refine ⟨c, T, hc0, hT0, fun t ht => ?_, ?_⟩
  · obtain ⟨⟨hcb, hTb⟩, hdc, hdT⟩ := hsol t ht
    rw [hcc] at hcb
    rw [hcc, hce, hfl] at hTb
    exact ⟨⟨hcb, hTb⟩, hdc, hdT⟩
  · rw [hc0, hT0]
    unfold arrheniusRateConstant
    positivity

/-- Dropping positive inlet and coolant temperatures: with `Tin = Tc = 0` the floor is `0`, not
positive, and the extended rate with this floor is discontinuous at `T = 0`. -/
lemma zeroInlet_floor_fixture :
    temperatureFloor 1 1 0 0 1 = 0 ∧ ¬ ContinuousAt (flooredRateConstant 1 1 0) 0 := by
  refine ⟨by norm_num [temperatureFloor], fun hcont => ?_⟩
  have h1 : Filter.Tendsto (flooredRateConstant 1 1 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [flooredRateConstant, arrheniusRateConstant] using this
  have h2 : Filter.Tendsto (flooredRateConstant 1 1 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
    refine hexp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with T hT
    have hT' : (0 : ℝ) < T := hT
    simp [flooredRateConstant, arrheniusRateConstant, max_eq_right hT'.le, div_eq_mul_inv]
  exact one_ne_zero (tendsto_nhds_unique h1 h2)

/-- Dropping the exothermic condition: for `b = -1` (with `a = 1`, `h = 0`, `A = B = 1`,
`Tin = Tc = 1`, `c0 = T0 = 1`) the floor is `Tmin = 1`, the temperature rate at the corner
`(1, Tmin)` is negative, and every temperature path through that corner drops below `Tmin`. -/
lemma endothermic_floor_fixture {T : ℝ → ℝ} {c : ℝ → ℝ} (hcI : c 0 = 1) (hTI : T 0 = 1)
    (hT : HasDerivWithinAt T
      (temperatureRhs 1 (-1) 0 1 1 (arrheniusRateConstant 1 1 (T 0)) (c 0) (T 0)) (Set.Ici 0) 0) :
    temperatureFloor 1 0 1 1 1 = 1 ∧
      temperatureRhs 1 (-1) 0 1 1 (arrheniusRateConstant 1 1 1) 1 1 < 0 ∧
      ∃ t > 0, T t < temperatureFloor 1 0 1 1 1 := by
  have hfl : temperatureFloor 1 0 1 1 1 = 1 := by norm_num [temperatureFloor]
  have hneg : temperatureRhs 1 (-1) 0 1 1 (arrheniusRateConstant 1 1 1) 1 1 < 0 := by
    unfold temperatureRhs arrheniusRateConstant
    have := Real.exp_pos (-1 / 1)
    nlinarith
  refine ⟨hfl, hneg, ?_⟩
  rw [hcI, hTI] at hT
  rw [hasDerivWithinAt_iff_tendsto_slope] at hT
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext s
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne h1 (Ne.symm h2)
    · intro h
      exact ⟨h.le, h.ne'⟩
  rw [hset] at hT
  have hev := hT.eventually (gt_mem_nhds hneg)
  obtain ⟨t, ht_slope, ht_pos⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨t, ht_pos, ?_⟩
  have ht0 : (0 : ℝ) < t := ht_pos
  rw [slope_def_field, hTI, sub_zero] at ht_slope
  rw [hfl]
  have : T t - 1 < 0 := by
    by_contra hge
    have := div_nonneg (not_lt.mp hge) ht0.le
    linarith
  linarith

-- Every forward solution from the interior state `(1/2, 3/2)` stays in `[0, 1] × [1, 2]`.
example {c T : ℝ → ℝ} (hcI : c 0 = 1 / 2) (hTI : T 0 = 3 / 2)
    (hc : ∀ s, 0 ≤ s → HasDerivWithinAt c
      (concentrationRhs 1 1 (arrheniusRateConstant 1 1 (T s)) (c s)) (Set.Ici 0) s)
    (hT : ∀ s, 0 ≤ s → HasDerivWithinAt T
      (temperatureRhs 1 2 1 1 1 (arrheniusRateConstant 1 1 (T s)) (c s) (T s)) (Set.Ici 0) s)
    {t : ℝ} (ht : 0 ≤ t) : c t ∈ Set.Icc 0 1 ∧ T t ∈ Set.Icc 1 2 := by
  obtain ⟨hcc, hfl, hce, -, -, -⟩ := interiorReaction_fixture
  have h := arrhenius_box_invariant (a := 1) (b := 2) (h := 1) (A := 1) (B := 1) (cin := 1)
    (Tin := 1) (Tc := 1) one_pos one_pos (by norm_num) zero_le_one zero_le_two zero_le_one
    zero_le_one (by norm_num) hcI hTI hc hT ht
  rw [hcc, hce, hfl] at h
  exact h

-- On the floor face `T = 1` of the fixture box, at `c = 1/2`, the temperature rate is
-- nonnegative: the face points into the box.
example : 0 ≤ temperatureRhs 1 2 1 1 1 (arrheniusRateConstant 1 1 1) (1 / 2) 1 := by
  have hk := arrheniusRateConstant_nonneg (A := 1) zero_le_one 1 1
  have hkA := arrheniusRateConstant_le (A := 1) (B := 1) (T := 1) zero_le_one zero_le_one one_pos
  exact (box_face_signs (a := 1) (b := 2) (h := 1) (A := 1) (cin := 1) (Tin := 1) (Tc := 1)
    (c0 := 1 / 2) (T0 := 3 / 2) one_pos zero_le_one zero_le_two zero_le_one hk hkA
    (by norm_num [concentrationCeiling])).2.2.1 (by norm_num [temperatureFloor])

-- The extended rate equals the Arrhenius rate at a box temperature and stays in `[0, 1]` far
-- below the floor.
example : flooredRateConstant 1 1 1 (3 / 2) = arrheniusRateConstant 1 1 (3 / 2) ∧
    flooredRateConstant 1 1 1 (-5) ∈ Set.Icc 0 1 :=
  ⟨flooredRateConstant_eq zero_le_one (by norm_num),
    flooredRateConstant_mem_Icc zero_le_one zero_le_one one_pos (-5)⟩

-- The fixture floor is positive, and the extended fixture field is continuous.
example : 0 < temperatureFloor 1 1 1 1 (3 / 2) ∧
    Continuous
      (cstrField 1 2 1 1 1 1 (flooredRateConstant 1 1 (temperatureFloor 1 1 1 1 (3 / 2)))) := by
  have hpos := temperatureFloor_pos (a := 1) (h := 1) (Tin := 1) (Tc := 1) (T0 := 3 / 2)
    one_pos zero_le_one one_pos one_pos (by norm_num)
  exact ⟨hpos, (locallyLipschitz_cstrField_flooredRateConstant 1 2 1 1 1 1 1 1 hpos).continuous⟩

-- The comparison holds for any rate law with values in `[0, A]`: a constant rate `1/2` on the
-- fixture box, over `[0, 1]`.
example {c T : ℝ → ℝ} (hcI : c 0 = 1 / 2) (hTI : T 0 = 3 / 2)
    (hc : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt c (concentrationRhs 1 1 (1 / 2) (c s)) (Set.Icc 0 1) s)
    (hT : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt T (temperatureRhs 1 2 1 1 1 (1 / 2) (c s) (T s)) (Set.Icc 0 1) s) :
    c 1 ∈ Set.Icc 0 (concentrationCeiling (1 / 2) 1) ∧
      T 1 ∈ Set.Icc (temperatureFloor 1 1 1 1 (3 / 2))
        (temperatureCeiling 1 2 1 1 1 1 (3 / 2) (concentrationCeiling (1 / 2) 1)) :=
  box_invariant_of_rate_bounds (κ := fun _ => 1 / 2) one_pos zero_le_one zero_le_two
    zero_le_one (by norm_num) (by norm_num) (fun _ => by norm_num) (fun _ _ => by norm_num)
    hcI hTI hc hT zero_le_one

end PhyslibExtTest.Chemistry.ReactingTransportPorts

end
