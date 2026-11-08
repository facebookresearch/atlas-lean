/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.Grover.Analysis
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Standard iteration choice for Grover search

For `θ = arcsin (sqrt (m / N))`, choose `⌊π / (4θ)⌋` Grover iterations.
The resulting phase is within `θ` of `π / 2`, so the failure probability is at
most `sin² θ = m / N`. The iteration count is at most the usual
`(π / 4) sqrt (N / m)` bound.
-/

@[expose] public section

namespace Cslib.Grover

theorem groverAngle_pos {α : Type*} [Fintype α]
    (marked : Finset α) (hMarked : marked.Nonempty) :
    0 < groverAngle marked := by
  have hmpos : 0 < (marked.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hMarked)
  have hcard : marked.card ≤ Fintype.card α := marked.card_le_univ
  have hnpos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (Finset.card_pos.mpr hMarked) hcard
  rw [groverAngle, Real.arcsin_pos]
  exact Real.sqrt_pos.2 (div_pos hmpos hnpos)

theorem groverAngle_le_pi_div_two {α : Type*} [Fintype α]
    (marked : Finset α) : groverAngle marked ≤ Real.pi / 2 := by
  exact Real.arcsin_le_pi_div_two _

theorem sin_sq_groverAngle {α : Type*} [Fintype α]
    (marked : Finset α) (hMarked : marked.Nonempty) :
    Real.sin (groverAngle marked) ^ 2 =
      (marked.card : ℝ) / Fintype.card α := by
  have hm : 0 ≤ (marked.card : ℝ) := by positivity
  have hn : 0 ≤ (Fintype.card α : ℝ) := by positivity
  have hnpos : 0 < (Fintype.card α : ℝ) := by
    have hcard : marked.card ≤ Fintype.card α := marked.card_le_univ
    exact_mod_cast lt_of_lt_of_le (Finset.card_pos.mpr hMarked) hcard
  rw [sin_groverAngle marked hMarked, div_pow, Real.sq_sqrt hm,
    Real.sq_sqrt hn]

/-- Standard integer choice `⌊π / (4θ)⌋` for known marked count. -/
noncomputable def floorIterations {α : Type*} [Fintype α]
    (marked : Finset α) : ℕ :=
  ⌊Real.pi / (4 * groverAngle marked)⌋₊

theorem floorIterations_phase_distance {α : Type*} [Fintype α]
    (marked : Finset α) (hMarked : marked.Nonempty) :
    |groverPhase marked (floorIterations marked) - Real.pi / 2| ≤
      groverAngle marked := by
  have hθpos := groverAngle_pos marked hMarked
  have hdenpos : 0 < 4 * groverAngle marked := mul_pos (by norm_num) hθpos
  have hxnonneg : 0 ≤ Real.pi / (4 * groverAngle marked) :=
    div_nonneg Real.pi_pos.le hdenpos.le
  have hfloor :
      (floorIterations marked : ℝ) ≤
        Real.pi / (4 * groverAngle marked) := by
    exact Nat.floor_le hxnonneg
  have hnext :
      Real.pi / (4 * groverAngle marked) <
        (floorIterations marked : ℝ) + 1 := by
    exact Nat.lt_floor_add_one _
  have hfloorMul :
      (floorIterations marked : ℝ) * (4 * groverAngle marked) ≤
        Real.pi :=
    (le_div_iff₀ hdenpos).mp hfloor
  have hnextMul :
      Real.pi < ((floorIterations marked : ℝ) + 1) *
        (4 * groverAngle marked) :=
    (div_lt_iff₀ hdenpos).mp hnext
  rw [abs_le]
  constructor <;> simp only [groverPhase] <;> nlinarith

theorem floorIterations_le_sqrt_ratio {α : Type*} [Fintype α]
    (marked : Finset α) (hMarked : marked.Nonempty) :
    (floorIterations marked : ℝ) ≤
      Real.pi / 4 *
        Real.sqrt ((Fintype.card α : ℝ) / marked.card) := by
  have hθpos := groverAngle_pos marked hMarked
  have hsinpos : 0 < Real.sin (groverAngle marked) := by
    have hmpos : 0 < (marked.card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr hMarked)
    have hcard : marked.card ≤ Fintype.card α := marked.card_le_univ
    have hnpos : 0 < (Fintype.card α : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (Finset.card_pos.mpr hMarked) hcard
    rw [sin_groverAngle marked hMarked]
    exact div_pos (Real.sqrt_pos.2 hmpos) (Real.sqrt_pos.2 hnpos)
  have hsinle : Real.sin (groverAngle marked) ≤ groverAngle marked :=
    Real.sin_le hθpos.le
  have hfloor :
      (floorIterations marked : ℝ) ≤
        Real.pi / (4 * groverAngle marked) := by
    exact Nat.floor_le (div_nonneg Real.pi_pos.le (by positivity))
  have hratio :
      Real.pi / (4 * groverAngle marked) ≤
        Real.pi / (4 * Real.sin (groverAngle marked)) := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
    nlinarith
  calc
    (floorIterations marked : ℝ) ≤
        Real.pi / (4 * groverAngle marked) := hfloor
    _ ≤ Real.pi / (4 * Real.sin (groverAngle marked)) := hratio
    _ = Real.pi / 4 *
        Real.sqrt ((Fintype.card α : ℝ) / marked.card) := by
      have hmpos : 0 < (marked.card : ℝ) := by
        exact_mod_cast (Finset.card_pos.mpr hMarked)
      have hcard : marked.card ≤ Fintype.card α := marked.card_le_univ
      have hnpos : 0 < (Fintype.card α : ℝ) := by
        exact_mod_cast lt_of_lt_of_le (Finset.card_pos.mpr hMarked) hcard
      have hsm0 : Real.sqrt (marked.card : ℝ) ≠ 0 :=
        (Real.sqrt_pos.2 hmpos).ne'
      have hsn0 : Real.sqrt (Fintype.card α : ℝ) ≠ 0 :=
        (Real.sqrt_pos.2 hnpos).ne'
      rw [sin_groverAngle marked hMarked, Real.sqrt_div hnpos.le]
      field_simp

/-- If exactly one quarter of the search space is marked, one Grover iteration
succeeds with probability one. -/
theorem one_step_success_of_four_mul_card_eq {α : Type*} [Fintype α]
    [DecidableEq α] (marked : Finset α) (hMarked : marked.Nonempty)
    (hquarter : 4 * marked.card = Fintype.card α) :
    markedProbability marked
        (groverIterate marked 1 (uniformAmplitude α)) = 1 := by
  have hmpos : 0 < (marked.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hMarked)
  have hnpos : 0 < (Fintype.card α : ℝ) := by
    have hmNat : 0 < marked.card := Finset.card_pos.mpr hMarked
    have hnNat : 0 < Fintype.card α := by omega
    exact_mod_cast hnNat
  have hcard :
      (Fintype.card α : ℝ) = (marked.card : ℝ) + (markedᶜ.card : ℝ) := by
    exact_mod_cast (Finset.card_add_card_compl marked).symm
  have hquarterReal :
      (4 : ℝ) * marked.card = Fintype.card α := by
    exact_mod_cast hquarter
  have hsqrtn0 : Real.sqrt (Fintype.card α : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hnpos).ne'
  simp only [groverIterate, Function.iterate_one]
  rw [uniformAmplitude_eq_symmetricAmplitude marked,
    markedProbability_groverStep_symmetricAmplitude]
  unfold markedAmplitudeNext oracleMean
  field_simp
  rw [Real.sq_sqrt hnpos.le]
  have hu : (markedᶜ.card : ℝ) = 3 * marked.card := by
    nlinarith [hcard, hquarterReal]
  rw [hu, ← hquarterReal]
  ring

theorem floorIterations_failure_probability_le {α : Type*} [Fintype α]
    [DecidableEq α] (marked : Finset α) (hMarked : marked.Nonempty)
    (hUnmarked : markedᶜ.Nonempty) :
    1 - markedProbability marked
        (groverIterate marked (floorIterations marked) (uniformAmplitude α)) ≤
      (marked.card : ℝ) / Fintype.card α := by
  let θ := groverAngle marked
  let phase := groverPhase marked (floorIterations marked)
  have hθpos : 0 < θ := groverAngle_pos marked hMarked
  have hθle : θ ≤ Real.pi / 2 := groverAngle_le_pi_div_two marked
  have hdist : |phase - Real.pi / 2| ≤ θ :=
    floorIterations_phase_distance marked hMarked
  have hbounds := abs_le.mp hdist
  have hupper : Real.sin (phase - Real.pi / 2) ≤ Real.sin θ := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · exact hθle
    · exact hbounds.2
  have hlower : -Real.sin θ ≤ Real.sin (phase - Real.pi / 2) := by
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two
      (x := -θ) (y := phase - Real.pi / 2) (by nlinarith [hθle, Real.pi_pos])
      (by nlinarith [hbounds.2, hθle]) hbounds.1
    simpa using h
  have hsinθ : 0 ≤ Real.sin θ := by
    exact Real.sin_nonneg_of_nonneg_of_le_pi hθpos.le
      (by nlinarith [hθle, Real.pi_pos])
  have hsquare :
      Real.sin (phase - Real.pi / 2) ^ 2 ≤ Real.sin θ ^ 2 := by
    nlinarith
  have hshift :
      Real.sin (phase - Real.pi / 2) ^ 2 = Real.cos phase ^ 2 := by
    rw [Real.sin_sub_pi_div_two]
    ring
  have hcircle := Real.sin_sq_add_cos_sq phase
  rw [markedProbability_groverIterate_uniform marked hMarked hUnmarked]
  change 1 - Real.sin phase ^ 2 ≤ _
  rw [← sin_sq_groverAngle marked hMarked]
  change 1 - Real.sin phase ^ 2 ≤ Real.sin θ ^ 2
  nlinarith

end Cslib.Grover
