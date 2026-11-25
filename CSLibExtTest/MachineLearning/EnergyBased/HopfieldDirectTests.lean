/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.EnergyBased.Hopfield
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

open Finset MeasureTheory ProbabilityTheory
open MathlibExt.GameTheory.PotentialGame
open scoped BigOperators Matrix ENat

namespace Cslib.MachineLearning.Hopfield.DirectTests

noncomputable def thresholdWeights : Fin 2 → Fin 2 → ℝ := !![0, -1; -1, 0]
def thresholds : Fin 2 → ℝ := ![-2, 0]
def thresholdStart : Fin 2 → Bool := ![false, true]
def thresholdAfter : Fin 2 → Bool := ![true, true]
def thresholdStable : Fin 2 → Bool := ![true, false]

theorem threshold_symmetric : Matrix.IsSymm thresholdWeights := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

theorem threshold_field : localField thresholdWeights thresholdStart 0 = -1 := by
  norm_num [localField, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ,
    thresholdWeights, thresholdStart]

theorem threshold_step : step thresholdWeights thresholds 0 thresholdStart = thresholdAfter := by
  rw [step, threshold_field]
  norm_num [thresholds]
  funext j
  fin_cases j <;> simp [thresholdStart, thresholdAfter, Function.update]

theorem threshold_changed : step thresholdWeights thresholds 0 thresholdStart ≠ thresholdStart := by
  rw [threshold_step]
  intro h
  exact Bool.noConfusion (congrFun h 0)

theorem threshold_energies : energy thresholdWeights thresholdStart = 0 ∧
    energy thresholdWeights thresholdAfter = 1 ∧
    energyWithThreshold thresholdWeights thresholds thresholdStart = 0 ∧
    energyWithThreshold thresholdWeights thresholds thresholdAfter = -1 := by
  norm_num [energyWithThreshold, energy, Finset.sum_erase_eq_sub (mem_univ _),
    Fin.sum_univ_succ, thresholdWeights, thresholds, thresholdStart, thresholdAfter]

theorem threshold_costs : cost thresholdWeights thresholds 0 thresholdStart = 0 ∧
    cost thresholdWeights thresholds 0 thresholdAfter = -1 := by
  norm_num [cost, localField, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ,
    thresholdWeights, thresholds, thresholdStart, thresholdAfter]

theorem threshold_cost_difference :
    cost thresholdWeights thresholds 0 (Function.update thresholdStart 0 true) -
        cost thresholdWeights thresholds 0 thresholdStart =
      energyWithThreshold thresholdWeights thresholds (Function.update thresholdStart 0 true) -
        energyWithThreshold thresholdWeights thresholds thresholdStart := by
  exact isExactPotential_energyWithThreshold threshold_symmetric thresholdStart 0 true

theorem threshold_update_identity :
    energyWithThreshold thresholdWeights thresholds (Function.update thresholdStart 0 true) -
        energyWithThreshold thresholdWeights thresholds thresholdStart =
      -((true.toNat : ℝ) - (thresholdStart 0).toNat) *
        (localField thresholdWeights thresholdStart 0 - thresholds 0) := by
  exact energyWithThreshold_update threshold_symmetric thresholdStart 0 true

theorem threshold_decrease :
    energyWithThreshold thresholdWeights thresholds (step thresholdWeights thresholds 0 thresholdStart) <
      energyWithThreshold thresholdWeights thresholds thresholdStart := by
  exact energyWithThreshold_step_lt threshold_symmetric threshold_changed

theorem threshold_improving : ImprovingMove (S := fun _ : Fin 2 => Bool)
    (cost thresholdWeights thresholds) (step thresholdWeights thresholds 0 thresholdStart)
    thresholdStart := by
  exact improvingMove_of_step_ne threshold_changed

theorem threshold_stable : Stable thresholdWeights thresholds thresholdStable := by
  intro i
  fin_cases i <;>
    norm_num [step, localField, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ,
      thresholdWeights, thresholds, thresholdStable, ← Function.update_eq_self]

theorem threshold_local_minimum : ∀ i,
    energyWithThreshold thresholdWeights thresholds thresholdStable ≤
      energyWithThreshold thresholdWeights thresholds
        (Function.update thresholdStable i (!thresholdStable i)) := by
  exact (stable_iff_energyWithThreshold_le_flip threshold_symmetric thresholdStable).mp
    threshold_stable

def roundRobinTwo (k : ℕ) : Fin 2 := ⟨k % 2, Nat.mod_lt k (by decide)⟩

theorem roundRobinTwo_fair : Fair roundRobinTwo := by
  intro i K
  refine ⟨K * 2 + i.val, by omega, Fin.ext ?_⟩
  change (K * 2 + i.val) % 2 = i.val
  have := i.isLt
  omega

theorem threshold_stable_tail :
    ∃ K, Stable thresholdWeights thresholds
        (trajectory thresholdWeights thresholds roundRobinTwo thresholdStart K) ∧
      ∀ k ≥ K, trajectory thresholdWeights thresholds roundRobinTwo thresholdStart k =
        trajectory thresholdWeights thresholds roundRobinTwo thresholdStart K := by
  exact exists_stable_tail threshold_symmetric roundRobinTwo_fair thresholdStart

noncomputable def traceWeights : Fin 3 → Fin 3 → ℝ :=
  !![0, 1, -1; 1, 0, 1; -1, 1, 0]
def traceStart : Fin 3 → Bool := ![true, false, true]
def traceMiddle : Fin 3 → Bool := ![false, false, true]
def traceStable : Fin 3 → Bool := ![false, true, true]
def roundRobinThree (k : ℕ) : Fin 3 := ⟨k % 3, Nat.mod_lt k (by decide)⟩
noncomputable def trace : ℕ → Fin 3 → Bool :=
  trajectory traceWeights 0 roundRobinThree traceStart

theorem trace_symmetric : Matrix.IsSymm traceWeights := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

theorem roundRobinThree_fair : Fair roundRobinThree := by
  intro i K
  refine ⟨K * 3 + i.val, by omega, Fin.ext ?_⟩
  change (K * 3 + i.val) % 3 = i.val
  have := i.isLt
  omega

theorem trace_first_step : step traceWeights 0 0 traceStart = traceMiddle := by
  funext j
  fin_cases j <;>
    norm_num [step, localField, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ,
      traceWeights, traceStart, traceMiddle, Function.update]

theorem trace_one : trace 1 = traceMiddle := by
  exact trace_first_step

theorem trace_two : trace 2 = traceStable := by
  change step traceWeights 0 1 (trace 1) = traceStable
  rw [trace_one]
  funext j
  fin_cases j <;>
    norm_num [step, localField, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ,
      traceWeights, traceMiddle, traceStable, Function.update]

theorem trace_stable : Stable traceWeights 0 traceStable := by
  intro i
  fin_cases i <;>
    norm_num [step, localField, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ,
      traceWeights, traceStable, ← Function.update_eq_self]

theorem trace_start_unstable : ¬ Stable traceWeights 0 traceStart := by
  intro h
  have he := congrFun (h 0) 0
  rw [trace_first_step] at he
  exact Bool.noConfusion he

theorem trace_first_changed : step traceWeights 0 0 traceStart ≠ traceStart := by
  rw [trace_first_step]
  intro h
  exact Bool.noConfusion (congrFun h 0)

theorem trace_energies : energy traceWeights (trace 0) = 1 ∧
    energy traceWeights (trace 1) = 0 ∧ energy traceWeights (trace 2) = -1 := by
  rw [trace_one, trace_two]
  change energy traceWeights traceStart = 1 ∧ _
  norm_num [energy, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ,
    traceWeights, traceStart, traceMiddle, traceStable]

theorem trace_update_identity :
    energy traceWeights (Function.update (trace 0) (roundRobinThree 0) false) -
        energy traceWeights (trace 0) =
      -((false.toNat : ℝ) - (trace 0 (roundRobinThree 0)).toNat) *
        localField traceWeights (trace 0) (roundRobinThree 0) := by
  exact energy_update trace_symmetric (trace 0) (roundRobinThree 0) false

theorem trace_energy_decrease : energy traceWeights (trace 1) < energy traceWeights (trace 0) := by
  exact energy_step_lt trace_symmetric trace_first_changed

theorem trace_nash : IsPureNash (S := fun _ : Fin 3 => Bool)
    (cost traceWeights 0) traceStable := by
  exact (stable_iff_isPureNash traceStable).mp trace_stable

theorem trace_start_not_nash : ¬ IsPureNash (S := fun _ : Fin 3 => Bool)
    (cost traceWeights 0) traceStart := by
  exact fun h => trace_start_unstable ((stable_iff_isPureNash traceStart).mpr h)

theorem trace_local_minimum : ∀ i, energy traceWeights traceStable ≤
    energy traceWeights (Function.update traceStable i (!traceStable i)) := by
  exact (stable_iff_energy_le_flip trace_symmetric traceStable).mp trace_stable

theorem trace_from_two (k : ℕ) (hk : 2 ≤ k) : trace k = traceStable := by
  induction k, hk using Nat.le_induction with
  | base => exact trace_two
  | succ k hk ih =>
    change step traceWeights 0 (roundRobinThree k) (trace k) = traceStable
    rw [ih, trace_stable]

theorem trace_zero_change : 0 ∈ changeTimes traceWeights 0 roundRobinThree traceStart := by
  exact trace_first_changed

theorem trace_one_change : 1 ∈ changeTimes traceWeights 0 roundRobinThree traceStart := by
  change trace 2 ≠ trace 1
  rw [trace_two, trace_one]
  intro h
  exact Bool.noConfusion (congrFun h 1)

theorem trace_no_later_change (k : ℕ) (hk : 2 ≤ k) :
    k ∉ changeTimes traceWeights 0 roundRobinThree traceStart := by
  change ¬ trace (k + 1) ≠ trace k
  rw [trace_from_two k hk, trace_from_two (k + 1) (by omega)]
  simp

theorem trace_changeTimes : changeTimes traceWeights 0 roundRobinThree traceStart = {0, 1} := by
  ext k
  constructor
  · intro hk
    have : k < 2 := by
      by_contra h
      exact trace_no_later_change k (by omega) hk
    have : k = 0 ∨ k = 1 := by omega
    simpa using this
  · intro hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl
    · exact trace_zero_change
    · exact trace_one_change

theorem trace_change_count : (changeTimes traceWeights 0 roundRobinThree traceStart).encard = 2 := by
  rw [trace_changeTimes]
  rw [Set.encard_insert_of_notMem (by simp), Set.encard_singleton]
  rfl

theorem trace_change_bound :
    (changeTimes traceWeights 0 roundRobinThree traceStart).encard = 2 ∧
      (changeTimes traceWeights 0 roundRobinThree traceStart).encard ≤ ((2 ^ 3 - 1 : ℕ) : ℕ∞) := by
  exact ⟨trace_change_count, encard_changeTimes_le trace_symmetric roundRobinThree traceStart⟩

theorem trace_constant_tail : ∃ K, ∀ k ≥ K,
    trajectory traceWeights 0 roundRobinThree traceStart k =
      trajectory traceWeights 0 roundRobinThree traceStart K := by
  exact exists_constant_tail trace_symmetric roundRobinThree traceStart

theorem trace_stable_tail :
    ∃ K, Stable traceWeights 0 (trajectory traceWeights 0 roundRobinThree traceStart K) ∧
      ∀ k ≥ K, trajectory traceWeights 0 roundRobinThree traceStart k =
        trajectory traceWeights 0 roundRobinThree traceStart K := by
  exact exists_stable_tail_zero trace_symmetric roundRobinThree_fair traceStart

noncomputable def asymmetricWeights : Fin 3 → Fin 3 → ℝ :=
  !![0, -1, 1; 1, 0, -1; -1, 1, 0]
def asymmetricStart : Fin 3 → Bool := ![false, false, true]
def cycleStates : Fin 17 → Fin 3 → Bool :=
  ![![false, false, true], ![true, false, true], ![true, false, true],
    ![true, false, false], ![true, false, false], ![true, true, false],
    ![true, true, false], ![false, true, false], ![false, true, false],
    ![false, true, true], ![false, true, true], ![false, false, true],
    ![false, false, true], ![true, false, true], ![true, false, true],
    ![true, false, false], ![true, false, false]]

theorem asymmetric_not_symmetric : ¬ Matrix.IsSymm asymmetricWeights := by
  intro h
  have he := h.apply 1 0
  norm_num [asymmetricWeights] at he

theorem cycle_steps (k : Fin 16) :
    step asymmetricWeights 0 (roundRobinThree k.val) (cycleStates k.castSucc) =
      cycleStates k.succ := by
  fin_cases k <;> funext j <;> fin_cases j <;>
    norm_num [step, localField, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ,
      asymmetricWeights, roundRobinThree, cycleStates, Function.update]

theorem asymmetric_trace (k : ℕ) (hk : k ≤ 16) :
    trajectory asymmetricWeights 0 roundRobinThree asymmetricStart k =
      cycleStates ⟨k, by omega⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [trajectory_succ, ih (by omega)]
    exact cycle_steps ⟨k, by omega⟩

def changeWitnesses : Finset ℕ := {0, 2, 4, 6, 8, 10, 12, 14}

theorem asymmetric_eight_changes : changeWitnesses.card = 8 ∧
    ∀ k ∈ changeWitnesses, k < 16 ∧ k ∈ changeTimes asymmetricWeights 0 roundRobinThree asymmetricStart := by
  constructor
  · decide
  · intro k hk
    simp only [changeWitnesses, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      constructor
    all_goals try omega
    all_goals
      change trajectory asymmetricWeights 0 roundRobinThree asymmetricStart (_ + 1) ≠
        trajectory asymmetricWeights 0 roundRobinThree asymmetricStart _
      rw [asymmetric_trace _ (by omega), asymmetric_trace _ (by omega)]
    all_goals
      intro h
      first
      | exact Bool.noConfusion (congrFun h 0)
      | exact Bool.noConfusion (congrFun h 1)
      | exact Bool.noConfusion (congrFun h 2)

theorem asymmetric_bound_fails :
    ¬ (changeTimes asymmetricWeights 0 roundRobinThree asymmetricStart).encard ≤
      ((2 ^ 3 - 1 : ℕ) : ℕ∞) := by
  have hs : (↑changeWitnesses : Set ℕ) ⊆
      changeTimes asymmetricWeights 0 roundRobinThree asymmetricStart :=
    fun k hk => (asymmetric_eight_changes.2 k hk).2
  have hle := Set.encard_mono hs
  rw [Set.encard_coe_eq_coe_finsetCard, asymmetric_eight_changes.1] at hle
  intro h
  have : (8 : ℕ∞) ≤ 7 := hle.trans (by simpa using h)
  norm_num at this

noncomputable def pairWeights : Fin 2 → Fin 2 → ℝ := !![0, 1; 1, 0]
def unfairStart : Fin 2 → Bool := ![true, false]
def unfairSchedule : ℕ → Fin 2 := fun _ => 0

theorem pair_symmetric : Matrix.IsSymm pairWeights := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

theorem unfair_not_fair : ¬ Fair unfairSchedule := by
  intro h
  obtain ⟨k, _, hk⟩ := h 1 0
  exact (by decide : (0 : Fin 2) ≠ 1) hk

theorem unfair_step : step pairWeights 0 0 unfairStart = unfairStart := by
  simp [step, localField, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ,
    pairWeights, unfairStart]

theorem unfair_constant (k : ℕ) :
    trajectory pairWeights 0 unfairSchedule unfairStart k = unfairStart := by
  induction k with
  | zero => rfl
  | succ k ih => rw [trajectory_succ, ih]; exact unfair_step

theorem unfair_not_stable : ¬ Stable pairWeights 0 unfairStart := by
  intro h
  have he := congrFun (h 1) 1
  norm_num [step, localField, Finset.sum_erase_eq_sub (mem_univ _), Fin.sum_univ_succ,
    pairWeights, unfairStart] at he

theorem unfair_constant_tail : ∃ K, ∀ k ≥ K,
    trajectory pairWeights 0 unfairSchedule unfairStart k =
      trajectory pairWeights 0 unfairSchedule unfairStart K := by
  exact exists_constant_tail pair_symmetric unfairSchedule unfairStart

noncomputable def uniformNeuron (N : ℕ) : Measure (Fin (N + 1)) :=
  Measure.uniformOfFinset univ

instance uniformNeuron_probability (N : ℕ) : IsProbabilityMeasure (uniformNeuron N) where
  measure_univ := by
    rw [uniformNeuron, Measure.uniformOfFinset_apply]
    simp [ENNReal.div_self]

noncomputable def randomMeasure (N : ℕ) : Measure (ℕ → Fin (N + 1)) :=
  Measure.infinitePi (fun _ : ℕ => uniformNeuron N)

instance randomMeasure_probability (N : ℕ) : IsProbabilityMeasure (randomMeasure N) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => uniformNeuron N)))

def randomSchedule (N : ℕ) (k : ℕ) (ω : ℕ → Fin (N + 1)) : Fin (N + 1) := ω k

theorem random_iid (N : ℕ) : IIDFullSupport (randomMeasure N) (randomSchedule N) := by
  refine ⟨measurable_pi_apply, ?_, ?_, ?_⟩
  · exact iIndepFun_infinitePi (fun _ => measurable_id)
  · intro k
    exact ⟨(measurable_pi_apply k).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      (Measure.infinitePi_map_eval _ k).trans
        (Measure.infinitePi_map_eval (fun _ : ℕ => uniformNeuron N) 0).symm⟩
  · intro i
    change 0 < Measure.infinitePi _ ((fun ω : ℕ → Fin (N + 1) => ω 0) ⁻¹' {i})
    rw [← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton i),
      Measure.infinitePi_map_eval]
    simp [uniformNeuron]

theorem random_two_fair : ∀ᵐ ω ∂randomMeasure 1, Fair (fun k => randomSchedule 1 k ω) := by
  exact ae_fair (random_iid 1)

theorem random_three_fair : ∀ᵐ ω ∂randomMeasure 2, Fair (fun k => randomSchedule 2 k ω) := by
  exact ae_fair (random_iid 2)

theorem random_threshold_tail : ∀ᵐ ω ∂randomMeasure 1,
    ∃ K, Stable thresholdWeights thresholds
        (trajectory thresholdWeights thresholds (fun k => randomSchedule 1 k ω) thresholdStart K) ∧
      ∀ k ≥ K, trajectory thresholdWeights thresholds (fun n => randomSchedule 1 n ω) thresholdStart k =
        trajectory thresholdWeights thresholds (fun n => randomSchedule 1 n ω) thresholdStart K := by
  exact ae_exists_stable_tail threshold_symmetric (random_iid 1) thresholdStart

theorem random_zero_tail : ∀ᵐ ω ∂randomMeasure 2,
    ∃ K, Stable traceWeights 0
        (trajectory traceWeights 0 (fun k => randomSchedule 2 k ω) traceStart K) ∧
      ∀ k ≥ K, trajectory traceWeights 0 (fun n => randomSchedule 2 n ω) traceStart k =
        trajectory traceWeights 0 (fun n => randomSchedule 2 n ω) traceStart K := by
  exact ae_exists_stable_tail_zero trace_symmetric (random_iid 2) traceStart

#print axioms thresholdWeights
#print axioms thresholds
#print axioms thresholdStart
#print axioms thresholdAfter
#print axioms thresholdStable
#print axioms threshold_symmetric
#print axioms threshold_field
#print axioms threshold_step
#print axioms threshold_changed
#print axioms threshold_energies
#print axioms threshold_costs
#print axioms threshold_cost_difference
#print axioms threshold_update_identity
#print axioms threshold_decrease
#print axioms threshold_improving
#print axioms threshold_stable
#print axioms threshold_local_minimum
#print axioms roundRobinTwo
#print axioms roundRobinTwo_fair
#print axioms threshold_stable_tail
#print axioms traceWeights
#print axioms traceStart
#print axioms traceMiddle
#print axioms traceStable
#print axioms roundRobinThree
#print axioms trace
#print axioms trace_symmetric
#print axioms roundRobinThree_fair
#print axioms trace_first_step
#print axioms trace_one
#print axioms trace_two
#print axioms trace_stable
#print axioms trace_start_unstable
#print axioms trace_first_changed
#print axioms trace_energies
#print axioms trace_update_identity
#print axioms trace_energy_decrease
#print axioms trace_nash
#print axioms trace_start_not_nash
#print axioms trace_local_minimum
#print axioms trace_from_two
#print axioms trace_zero_change
#print axioms trace_one_change
#print axioms trace_no_later_change
#print axioms trace_changeTimes
#print axioms trace_change_count
#print axioms trace_change_bound
#print axioms trace_constant_tail
#print axioms trace_stable_tail
#print axioms asymmetricWeights
#print axioms asymmetricStart
#print axioms cycleStates
#print axioms asymmetric_not_symmetric
#print axioms cycle_steps
#print axioms asymmetric_trace
#print axioms changeWitnesses
#print axioms asymmetric_eight_changes
#print axioms asymmetric_bound_fails
#print axioms pairWeights
#print axioms unfairStart
#print axioms unfairSchedule
#print axioms pair_symmetric
#print axioms unfair_not_fair
#print axioms unfair_step
#print axioms unfair_constant
#print axioms unfair_not_stable
#print axioms unfair_constant_tail
#print axioms uniformNeuron
#print axioms uniformNeuron_probability
#print axioms randomMeasure
#print axioms randomMeasure_probability
#print axioms randomSchedule
#print axioms random_iid
#print axioms random_two_fair
#print axioms random_three_fair
#print axioms random_threshold_tail
#print axioms random_zero_tail

end Cslib.MachineLearning.Hopfield.DirectTests
