/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.LadderDerivation

/-!
# Ladder derivation tests

* Pathwise: the first descending ladder epoch and excursion maximum of the scores `1, -2, 0, …`;
  the zero path has no descending ladder epoch (junk value `0`).
* The periodic scores `1, -2, 1, -2, …`: every excursion has length `2` and height `1`,
  `T_k = 2 k`, `N₅ = 2`, the path is ladder-good, and the sandwich lemmas apply.
* Measurability: an event of the first two scores lies in `pastMeasurableSpace 2`; the
  stopping-time theorem in Mathlib's `IsStoppingTime` form.
* A concrete instance of `CramerScores`: i.i.d. `±1` scores with `P(X = 1) = 1/4`, mean `-1/2`
  and Cramér root `θ = log 3` (`E e^{θ X} = 3/4 + 1/4 = 1`) on the infinite product space; the
  derived `LadderInput` (`toLadderInput`) has `A ≥ 1` and applies the `GumbelTail` sandwich.
-/

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance.LadderDerivation

open MeasureTheory ProbabilityTheory Finset

/-! ### Pathwise -/

example : pathShift 2 (fun k => (k : ℝ)) 1 = 3 := by norm_num [pathShift]

/-- The scores `1, -2, 0, 0, …`: walk `0, 1, -1, -1, …`. -/
noncomputable def x₁ : ℕ → ℝ := fun k => if k = 0 then 1 else if k = 1 then -2 else 0

example : HasDescLadder x₁ := ⟨2, by norm_num, by norm_num [x₁, sum_range_succ]⟩

theorem descLadderEpoch_x₁ : descLadderEpoch x₁ = 2 :=
  (hasDescLadder_and_descLadderEpoch_eq_iff.2 ⟨by norm_num, by norm_num [x₁, sum_range_succ],
    fun j hj0 hj2 => by
      interval_cases j
      norm_num [x₁]⟩).2

example : excursionMax x₁ = 1 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨j, hj, h⟩ := exists_sum_range_eq_excursionMax x₁
    rw [descLadderEpoch_x₁] at hj
    rw [← h]
    interval_cases j <;> norm_num [x₁, sum_range_succ]
  · have := sum_range_le_excursionMax (x := x₁) (j := 1) (by rw [descLadderEpoch_x₁]; norm_num)
    simpa [x₁] using this

example : ¬ HasDescLadder (fun _ => (0 : ℝ)) := by
  rintro ⟨k, _, hk⟩
  simp at hk

example : descLadderEpoch (fun _ => (0 : ℝ)) = 0 :=
  descLadderEpoch_eq_zero fun ⟨k, _, hk⟩ => by simp at hk

/-! ### Periodic scores `1, -2, 1, -2, …` -/

/-- The periodic scores `1, -2, 1, -2, …`. -/
noncomputable def xp : ℕ → ℝ := fun k => if Even k then 1 else -2

theorem pathShift_two_xp : pathShift 2 xp = xp := by
  ext j
  simp [xp, pathShift, Nat.even_add]

theorem descLadderEpoch_xp : descLadderEpoch xp = 2 :=
  (hasDescLadder_and_descLadderEpoch_eq_iff.2 ⟨by norm_num, by norm_num [xp, sum_range_succ],
    fun j hj0 hj2 => by
      interval_cases j
      norm_num [xp]⟩).2

theorem iterLadder_xp {α : Type*} (φ : (ℕ → ℝ) → α) (i : ℕ) : iterLadder φ i xp = φ xp := by
  induction i with
  | zero => rfl
  | succ i ih => rw [iterLadder, descLadderEpoch_xp, pathShift_two_xp, ih]

example (i : ℕ) : excursionLength i xp = 2 := by
  rw [excursionLength, iterLadder_xp, descLadderEpoch_xp]

theorem excursionMax_xp : excursionMax xp = 1 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨j, hj, h⟩ := exists_sum_range_eq_excursionMax xp
    rw [descLadderEpoch_xp] at hj
    rw [← h]
    interval_cases j <;> norm_num [xp, sum_range_succ]
  · have := sum_range_le_excursionMax (x := xp) (j := 1) (by rw [descLadderEpoch_xp]; norm_num)
    simpa [xp] using this

example (i : ℕ) : excursionHeight i xp = 1 := by
  rw [excursionHeight, iterLadder_xp, excursionMax_xp]

theorem ladderEpoch_xp (k : ℕ) : ladderEpoch k xp = 2 * k := by
  simp [ladderEpoch, excursionLength, iterLadder_xp, descLadderEpoch_xp, mul_comm]

theorem isLadderGood_xp : IsLadderGood xp := by
  intro t
  rcases Nat.even_or_odd t with ht | ht
  · exact ⟨2, by norm_num, by norm_num [xp, sum_range_succ, pathShift, Nat.even_add, ht]⟩
  · have hne : ¬ Even t := Nat.not_even_iff_odd.2 ht
    exact ⟨1, by norm_num, by norm_num [xp, pathShift, hne]⟩

example : ladderCount 5 xp = 2 := by
  refine le_antisymm ?_ ((le_ladderCount_iff isLadderGood_xp).2 (by rw [ladderEpoch_xp]; norm_num))
  by_contra h
  have := (le_ladderCount_iff isLadderGood_xp).1 (not_le.1 h)
  rw [ladderEpoch_xp] at this
  omega

example (n : ℕ) {i : ℕ} (hi : i < ladderCount n xp) :
    excursionHeight i xp ≤ maxSegmentScore xp n :=
  excursionHeight_le_maxSegmentScore isLadderGood_xp hi

example (n : ℕ) (h : ∀ i ≤ ladderCount n xp, excursionHeight i xp ≤ 1) :
    maxSegmentScore xp n ≤ 1 :=
  maxSegmentScore_le_of_forall isLadderGood_xp h

/-! ### Measurability and the stopping-time property -/

example : MeasurableSet[pastMeasurableSpace 2] {x : ℕ → ℝ | ∑ i ∈ range 2, x i < 0} :=
  measurableSet_lt (measurable_past_sum le_rfl) measurable_const

example : MeasurableSet[pastMeasurableSpace 3]
    {x : ℕ → ℝ | HasDescLadder x ∧ descLadderEpoch x = 3} :=
  measurableSet_descLadderEpoch_eq 3

open Classical in
example : IsStoppingTime (Filtration.natural (fun i (x : ℕ → ℝ) => x i)
      fun i => (measurable_pi_apply i).stronglyMeasurable)
      fun x => if HasDescLadder x then (descLadderEpoch x : WithTop ℕ) else ⊤ :=
  isStoppingTime_descLadderEpoch

/-- On the scores `1, -2, 0, …`, Mathlib's hitting time of `(-∞, 0)` after time `1` is `2`. -/
example : hittingAfter (fun k (x : ℕ → ℝ) => ∑ i ∈ range k, x i) (Set.Iio 0) 1 x₁ = 2 := by
  classical
  have h : HasDescLadder x₁ := ⟨2, by norm_num, by norm_num [x₁, sum_range_succ]⟩
  rw [← descLadderEpoch_eq_hittingAfter]
  simp [h, descLadderEpoch_x₁]

/-! ### A concrete Cramér score sequence: `±1` steps with `P(X = 1) = 1/4` -/

/-- The law of a `±1` score with `P(X = 1) = 1/4`, `P(X = -1) = 3/4`. -/
noncomputable def pm : Measure ℝ :=
  ENNReal.ofReal (1 / 4) • Measure.dirac 1 + ENNReal.ofReal (3 / 4) • Measure.dirac (-1)

instance : IsProbabilityMeasure pm := by
  constructor
  simp only [pm, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem integral_pm (f : ℝ → ℝ) : ∫ y, f y ∂pm = 1 / 4 * f 1 + 3 / 4 * f (-1) := by
  have hi : ∀ a : ℝ, Integrable f (Measure.dirac a) := fun a => integrable_dirac enorm_lt_top
  rw [pm, integral_add_measure ((hi 1).smul_measure ENNReal.ofReal_ne_top)
      ((hi (-1)).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
  simp [smul_eq_mul]

/-- The i.i.d. `±1` scores on the product space. -/
noncomputable abbrev Ppm : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => pm

theorem cramerScores_pm :
    CramerScores Ppm (fun i (x : ℕ → ℝ) => x i) (Real.log 3) where
  measurable i := measurable_pi_apply i
  iIndepFun := iIndepFun_infinitePi (X := fun _ (y : ℝ) => y) fun _ => measurable_id
  identDistrib i :=
    { aemeasurable_fst := (measurable_pi_apply i).aemeasurable
      aemeasurable_snd := (measurable_pi_apply 0).aemeasurable
      map_eq := by rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval] }
  integrable := by
    have h : Integrable id (Ppm.map fun x : ℕ → ℝ => x 0) := by
      rw [Measure.infinitePi_map_eval]
      exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top |>.add_measure
        ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)
    exact h.comp_measurable (measurable_pi_apply 0)
  integral_neg := by
    have h := integral_map (μ := Ppm) (φ := fun x : ℕ → ℝ => x 0)
      (measurable_pi_apply 0).aemeasurable (f := fun y : ℝ => y) measurable_id.aestronglyMeasurable
    rw [Measure.infinitePi_map_eval, integral_pm] at h
    rw [← h]
    norm_num
  pos := Real.log_pos (by norm_num)
  mgf_eq_one := by
    rw [← mgf_id_map (measurable_pi_apply 0).aemeasurable, Measure.infinitePi_map_eval, mgf,
      integral_pm]
    simp only [id, mul_one, mul_neg, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num

/-- The ladder input derived from the `±1` Cramér scores. -/
noncomputable def ladderPm : LadderInput Ppm (maxSegmentScoreRV fun i (x : ℕ → ℝ) => x i) :=
  cramerScores_pm.toLadderInput

example : 1 ≤ ladderPm.A := by
  rw [ladderPm, CramerScores.toLadderInput_A]
  exact cramerScores_pm.one_le_integral_descLadderEpoch

example : ladderPm.Y 3 = fun x => excursionHeight 3 x := rfl

example : ∀ᵐ x ∂Ppm, IsLadderGood x := cramerScores_pm.ae_isLadderGood

example (n m : ℕ) (t : ℝ) :
    Ppm.real {x | maxSegmentScoreRV (fun i (x : ℕ → ℝ) => x i) n x ≤ t} ≤
      ladderPm.F t ^ m + Ppm.real {x | ladderPm.N n x < m} :=
  ladderPm.real_le_le n m t

example : Nonempty (LadderInput Ppm (maxSegmentScoreRV fun i (x : ℕ → ℝ) => x i)) :=
  cramerScores_pm.nonempty_ladderInput

example : mgf id pm (Real.log 3 / 2) < 1 := by
  have h := cramerScores_pm.mgf_map_half_lt_one
  rwa [Measure.infinitePi_map_eval] at h

end Cslib.Bioinformatics.Alignment.ScoreSignificance.LadderDerivation
