/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.GroupSequentialFutility

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.GroupSequentialFutility

/-- Two equally spaced looks: information times `0, 1/2, 1, 1, …`. -/
noncomputable def τ₂ (k : ℕ) : ℝ := min ((k : ℝ) / 2) 1

theorem τ₂_zero : τ₂ 0 = 0 := by simp [τ₂]

theorem τ₂_mono : Monotone τ₂ := fun _ _ h =>
  min_le_min_right _ (div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num))

theorem τ₂_two : τ₂ 2 = 1 := by norm_num [τ₂]

/-- The linear spending function `β t`. -/
theorem isBetaSpendingFunction_linear {β : ℝ} (hβ : 0 ≤ β) :
    IsBetaSpendingFunction β (fun t => β * t) where
  map_zero := by simp
  monotoneOn := fun _ _ _ _ h => mul_le_mul_of_nonneg_left h hβ
  map_one_le := by simp

/-- Efficacy cutoffs: linear alpha spending at `α = 0.05` over two looks, `0.025` per look. -/
noncomputable abbrev c₂ : ℕ → ℝ := bonferroniLookLevel (fun t => 1 / 20 * t) τ₂

/-- Futility cutoffs: linear beta spending at `β = 0.2` over two looks, `0.1` per look. -/
noncomputable abbrev d₂ : ℕ → ℝ := bonferroniLookLevel (fun t => 1 / 5 * t) τ₂

/-! ### Cutoffs computed from the spending functions -/

example : c₂ 0 = 1 / 40 ∧ c₂ 1 = 1 / 40 := by
  constructor <;> norm_num [bonferroniLookLevel, τ₂]

example : d₂ 0 = 1 / 10 ∧ d₂ 1 = 1 / 10 := by
  constructor <;> norm_num [bonferroniLookLevel, τ₂]

/-! ### Concrete trials, decided from the definitions -/

/-- Efficacy p-values `0.5, 0.001` and futility p-values `0.05, 1`: the efficacy-only design
rejects at look 2, but the design with futility stops at look 1 (`0.05 ≤ 0.1`), so the
rejection is lost to a futility stop. -/
example : (rejectedLooks 2 c₂ fun k => if k = 0 then 1 / 2 else 1 / 1000).Nonempty ∧
    StopsForFutility 2 c₂ d₂ (fun k => if k = 0 then 1 / 2 else 1 / 1000)
      (fun k => if k = 0 then 1 / 20 else 1) ∧
    ¬RejectsWithFutility 2 c₂ d₂ (fun k => if k = 0 then 1 / 2 else 1 / 1000)
      (fun k => if k = 0 then 1 / 20 else 1) := by
  refine ⟨⟨1, ?_⟩, ⟨0, by norm_num, fun i hi => absurd hi (Nat.not_lt_zero i), ?_, ?_⟩, ?_⟩
  · simp only [rejectedLooks, Finset.mem_filter, Finset.mem_range]
    norm_num [bonferroniLookLevel, τ₂]
  · norm_num [bonferroniLookLevel, τ₂]
  · norm_num [bonferroniLookLevel, τ₂]
  · rintro ⟨j, hj, hcont, hp⟩
    interval_cases j
    · norm_num [bonferroniLookLevel, τ₂] at hp
    · have := (hcont 0 (by norm_num)).2
      norm_num [bonferroniLookLevel, τ₂] at this

/-- A strong early signal: efficacy p-value `0.001` at look 1 rejects before futility is
checked, even though the futility p-value `0.01` is below its cutoff. -/
example : RejectsWithFutility 2 c₂ d₂ (fun _ => 1 / 1000) (fun _ => 1 / 100) :=
  ⟨0, by norm_num, fun i hi => absurd hi (Nat.not_lt_zero i), by
    norm_num [bonferroniLookLevel, τ₂]⟩

/-- All p-values equal to one: the trial passes both looks without stopping. -/
example : ContinuesBefore c₂ d₂ (fun _ => 1) (fun _ => 1) 2 := by
  intro i hi
  interval_cases i <;> norm_num [bonferroniLookLevel, τ₂]

/-! ### The futility bound is attained -/

/-- One look, futility cutoff `1/4`, no efficacy rejection possible, futility p-value uniform on
`[0, 1]`: the futility-stop probability, computed from the definitions, is exactly `1/4`. -/
theorem futility_stop_uniform_eq :
    volume.restrict (Set.Icc (0 : ℝ) 1)
      {ω | StopsForFutility 1 (fun _ => 0) (fun _ => 1 / 4) (fun _ => 1) fun _ => ω} =
      ENNReal.ofReal (1 / 4) := by
  have hset : {ω : ℝ | StopsForFutility 1 (fun _ => 0) (fun _ => 1 / 4) (fun _ => 1)
      fun _ => ω} = Set.Iic (1 / 4) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_Iic, StopsForFutility, ContinuesBefore]
    constructor
    · rintro ⟨j, -, -, -, h⟩
      exact h
    · intro h
      exact ⟨0, one_pos, fun i hi => absurd hi (Nat.not_lt_zero i), one_pos, h⟩
  have hinter : Set.Iic (1 / 4 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 (1 / 4) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h, h0, -⟩
      exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩
      exact ⟨h, h0, by linarith⟩
  rw [hset, Measure.restrict_apply measurableSet_Iic, hinter, Real.volume_Icc]
  norm_num

/-- The uniform law on `[0, 1]` is a probability measure. -/
instance : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- Non-vacuity of `measure_stopsForFutility_le`: its hypotheses hold for the trial above with
the linear beta-spending function at `β = 1/4`, and its bound `1/4` equals the computed
futility-stop probability. -/
example :
    volume.restrict (Set.Icc (0 : ℝ) 1)
      {ω | StopsForFutility 1 (fun _ => 0) (bonferroniLookLevel (fun t => 1 / 4 * t)
        fun k => min (k : ℝ) 1) (fun _ => 1) fun _ => ω} ≤ ENNReal.ofReal (1 / 4) ∧
    bonferroniLookLevel (fun t => 1 / 4 * t) (fun k => min (k : ℝ) 1) 0 = 1 / 4 :=
  ⟨measure_stopsForFutility_le _ (fun _ _ => 1) (fun _ => id) _
    (isBetaSpendingFunction_linear (by norm_num)) (by norm_num) (by simp)
    (fun _ _ h => min_le_min_right _ (by exact_mod_cast h)) (by simp)
    fun _ _ => isValidPValue_of_hasLaw_uniform HasLaw.id,
   by norm_num [bonferroniLookLevel]⟩

/-! ### Error and power guarantees on a perfectly dependent trial -/

/-- Type-I error: every look reuses the same uniform efficacy p-value and any futility rule is
used; the design still rejects with probability at most `0.05`. -/
example (q : ℕ → ℝ → ℝ) :
    volume.restrict (Set.Icc (0 : ℝ) 1)
      {ω | RejectsWithFutility 2 c₂ d₂ (fun _ => ω) fun k => q k ω} ≤
      ENNReal.ofReal (1 / 20) :=
  measure_rejectsWithFutility_le _ (fun _ => id) q d₂
    (isBetaSpendingFunction_linear (by norm_num)) (by norm_num) τ₂_zero τ₂_mono τ₂_two.le
    fun _ _ => isValidPValue_of_hasLaw_uniform HasLaw.id

/-- Futility stops under the alternative: every look reuses the same uniform futility p-value;
the trial stops for futility with probability at most `0.2`. -/
example (p : ℕ → ℝ → ℝ) :
    volume.restrict (Set.Icc (0 : ℝ) 1)
      {ω | StopsForFutility 2 c₂ d₂ (fun k => p k ω) fun _ => ω} ≤ ENNReal.ofReal (1 / 5) :=
  measure_stopsForFutility_le _ p (fun _ => id) c₂
    (isBetaSpendingFunction_linear (by norm_num)) (by norm_num) τ₂_zero τ₂_mono τ₂_two.le
    fun _ _ => isValidPValue_of_hasLaw_uniform HasLaw.id

/-- Power cost of at most `0.2`. -/
example (p : ℕ → ℝ → ℝ) :
    volume.restrict (Set.Icc (0 : ℝ) 1) {ω | (rejectedLooks 2 c₂ fun k => p k ω).Nonempty} ≤
      volume.restrict (Set.Icc (0 : ℝ) 1)
        {ω | RejectsWithFutility 2 c₂ d₂ (fun k => p k ω) fun _ => ω} +
        ENNReal.ofReal (1 / 5) :=
  measure_rejectedLooks_nonempty_le_rejectsWithFutility_add _ p (fun _ => id) c₂
    (isBetaSpendingFunction_linear (by norm_num)) (by norm_num) τ₂_zero τ₂_mono τ₂_two.le
    fun _ _ => isValidPValue_of_hasLaw_uniform HasLaw.id

/-- Type-II error cost of at most `0.2`. -/
example (p : ℕ → ℝ → ℝ) :
    volume.restrict (Set.Icc (0 : ℝ) 1)
        {ω | ¬RejectsWithFutility 2 c₂ d₂ (fun k => p k ω) fun _ => ω} ≤
      volume.restrict (Set.Icc (0 : ℝ) 1) {ω | ¬(rejectedLooks 2 c₂ fun k => p k ω).Nonempty} +
        ENNReal.ofReal (1 / 5) :=
  measure_not_rejectsWithFutility_le_add _ p (fun _ => id) c₂
    (isBetaSpendingFunction_linear (by norm_num)) (by norm_num) τ₂_zero τ₂_mono τ₂_two.le
    fun _ _ => isValidPValue_of_hasLaw_uniform HasLaw.id

/-! ### Per-look futility levels can stop for futility with probability up to `K β` -/

/-- Some trial with two valid futility looks tested at `1/4` each stops for futility with
probability strictly above `1/4`. -/
example : ∃ (ν : Measure (Fin 4)) (q : ℕ → Fin 4 → ℝ), IsProbabilityMeasure ν ∧
    (∀ k < 2, IsValidPValue ν (q k)) ∧
    ENNReal.ofReal (1 / 4) <
      ν {ω | StopsForFutility 2 (fun _ => 0) (fun _ => 1 / 4) (fun _ => 1) fun k => q k ω} := by
  obtain ⟨ν, q, hν, hq, heq, hlt⟩ := exists_stopsForFutility_const_eq
  exact ⟨ν, q, hν, hq, heq ▸ hlt⟩

/-! ### Axioms -/

#print axioms measure_rejectsWithFutility_le
#print axioms measure_stopsForFutility_le
#print axioms measure_rejectedLooks_nonempty_le_rejectsWithFutility_add
#print axioms measure_not_rejectsWithFutility_le_add
#print axioms exists_stopsForFutility_const_eq
#print axioms rejectsWithFutility_or_stopsForFutility_or_continuesBefore
#print axioms futility_stop_uniform_eq

end MathlibExtTest.Probability.Statistics.MultipleTesting.GroupSequentialFutility
