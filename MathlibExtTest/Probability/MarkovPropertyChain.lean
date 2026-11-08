/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.StrongMarkovChain
public import Mathlib.Probability.Process.Stopping

import Mathlib.Tactic.NormNum

/-!
# Tests for the Markov and strong Markov properties for chains

Concrete instantiations of `markov_property_full` and
`strong_markov_chain` for the constant kernel on `Bool` with the
constant functional `Y = 1`, together with `#print axioms` checks
that the main theorems depend only on the standard axioms.

The additional finite-state fixture alternates two positive initial atoms and has a third null
state. It checks a coordinate at a positive shift, a nonconstant bounded stopping time with a
time-dependent bounded functional, and an a.s.-finite WithTop time that equals infinity on a
nonempty null event. The stopped observable is zero on the concrete constant-null-state path.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Kernel
open MathlibExt.Probability.MarkovChainPath
open MathlibExt.Probability.MarkovPropertyChain
open MathlibExt.Probability.StrongMarkovChain

namespace MathlibExtTest.Probability.MarkovPropertyChain

/-- The path measure of the constant `Bool` chain that jumps to `false` at every step,
started from `true`. -/
private noncomputable abbrev testMeasure : Measure (ℕ → Bool) :=
  MarkovChainPathMeasure Bool (Measure.dirac true) (Kernel.const Bool (Measure.dirac false))


/-- The Markov property applied to the constant functional `1` on `Bool`:
the conditional expectation is constantly `1`. -/
example :
    testMeasure[(fun _ : ℕ → Bool => (1 : ℝ)) ∘ shiftPath 0 | pathFiltration Bool 0]
    =ᵐ[testMeasure]
      fun _ => (1 : ℝ) := by
  have h := markov_property_full Bool (Measure.dirac true)
    (Kernel.const Bool (Measure.dirac false)) (fun _ : ℕ → Bool => (1 : ℝ))
    measurable_const ⟨1, fun _ => by simp⟩ 0
  simpa [markovExpectation, testMeasure] using h

/-- The strong Markov property applied to the constant functional `1` on `Bool`
at the constant stopping time `0`: the conditional expectation is constantly `1`. -/
example :
    testMeasure[fun _ : ℕ → Bool => (1 : ℝ) |
        (isStoppingTime_const (pathFiltration Bool) 0).measurableSpace]
    =ᵐ[testMeasure]
      fun _ => (1 : ℝ) := by
  have h := strong_markov_chain Bool (Measure.dirac true)
    (Kernel.const Bool (Measure.dirac false)) (fun _ : ℕ → Bool => 0)
    (isStoppingTime_const (pathFiltration Bool) 0)
    (fun (_ : ℕ) (_ : ℕ → Bool) => (1 : ℝ)) (fun _ => measurable_const)
    ⟨1, fun _ _ => by simp⟩
  simpa [markovExpectation, testMeasure] using h

namespace FiniteState

open scoped ENNReal

local instance : MeasurableSpace (Option Bool) := ⊤

/-- Two positive initial atoms and a third, explicit null state. -/
noncomputable def initial : Measure (Option Bool) :=
  (1 / 2 : ℝ≥0∞) •
    (Measure.dirac (some false : Option Bool) + Measure.dirac (some true : Option Bool))

instance initial_isProbabilityMeasure : IsProbabilityMeasure initial := by
  rw [isProbabilityMeasure_iff]
  norm_num [initial, Measure.smul_apply, Measure.add_apply]
  exact ENNReal.inv_two_add_inv_two

/-- The two supported states alternate; the null state is fixed. -/
noncomputable def transition : Kernel (Option Bool) (Option Bool) :=
  Kernel.deterministic (fun s : Option Bool => s.map Bool.not) (measurable_of_finite _)

instance transition_isMarkovKernel : IsMarkovKernel transition := by
  unfold transition
  infer_instance

/-- This fixture uses the existing construction, not a parallel path-measure definition. -/
noncomputable def chain : Measure (ℕ → Option Bool) :=
  MathlibExt.Probability.MarkovChainConstruction.markovChainMeasure transition initial

instance chain_isProbabilityMeasure : IsProbabilityMeasure chain := by
  unfold chain
  infer_instance

/-- A nonconstant coordinate functional whose index is one, rather than zero. -/
def coordinateOne (ω : ℕ → Option Bool) : ℝ := if ω 1 = some true then 1 else 0

lemma coordinateOne_measurable : Measurable coordinateOne :=
  (measurable_of_finite (fun s : Option Bool => if s = some true then (1 : ℝ) else 0)).comp
    (measurable_pi_apply 1)

lemma coordinateOne_bounded (ω : ℕ → Option Bool) : |coordinateOne ω| ≤ 1 := by
  unfold coordinateOne
  split_ifs <;> norm_num

/-- A time-dependent bounded functional; the null-state path always has value zero. -/
noncomputable def timedCoordinate (n : ℕ) (ω : ℕ → Option Bool) : ℝ :=
  if ω 1 = none then 0 else
    if n = 1 then coordinateOne ω else (1 / 2 : ℝ) + (1 / 2 : ℝ) * coordinateOne ω

lemma timedCoordinate_measurable (n : ℕ) : Measurable (timedCoordinate n) :=
  (measurable_of_finite (fun s : Option Bool =>
    if s = none then (0 : ℝ) else if n = 1 then (if s = some true then 1 else 0)
      else (1 / 2 : ℝ) + (1 / 2 : ℝ) * (if s = some true then 1 else 0))).comp
    (measurable_pi_apply 1)

lemma timedCoordinate_bounded (n : ℕ) (ω : ℕ → Option Bool) :
    |timedCoordinate n ω| ≤ 1 := by
  unfold timedCoordinate coordinateOne
  split_ifs <;> norm_num

private lemma eval_measurable (n i : ℕ) (hi : i ≤ n) :
    Measurable[pathFiltration (Option Bool) n] (fun ω : ℕ → Option Bool => ω i) := by
  rw [measurable_iff_comap_le]
  exact le_iSup₂ (f := fun (j : ℕ) (_ : j ≤ n) =>
    MeasurableSpace.comap (fun ω : ℕ → Option Bool => ω j)
      (inferInstance : MeasurableSpace (Option Bool))) i hi

private lemma initial_event (A : Set (Option Bool)) (hA : MeasurableSet A) :
    chain {ω | ω 0 ∈ A} = initial A := by
  have hmap : chain.map (fun ω : ℕ → Option Bool => ω 0) = initial :=
    MathlibExt.Probability.MarkovChainConstruction.markovChainMeasure_initial_distribution
      transition initial
  calc
    chain {ω | ω 0 ∈ A} = (chain.map (fun ω : ℕ → Option Bool => ω 0)) A :=
      (Measure.map_apply (measurable_pi_apply 0) hA).symm
    _ = initial A := congrArg (fun μ : Measure (Option Bool) => μ A) hmap

/-- The ordinary property sees coordinate two when the coordinate-one functional is shifted by one. -/
theorem coordinate_at_positive_shift :
    chain[(fun ω : ℕ → Option Bool => if ω 2 = some true then (1 : ℝ) else 0) |
        pathFiltration (Option Bool) 1]
      =ᵐ[chain] fun ω => markovExpectation (Option Bool) transition coordinateOne (ω 1) := by
  have h := markov_property_full (Option Bool) initial transition coordinateOne
    coordinateOne_measurable ⟨1, coordinateOne_bounded⟩ 1
  have hshift : coordinateOne ∘ shiftPath 1 =
      fun ω : ℕ → Option Bool => if ω 2 = some true then (1 : ℝ) else 0 := by
    funext ω
    rfl
  rw [hshift] at h
  exact h

/-- Both values occur with positive probability in the same chain. -/
def boundedTime (ω : ℕ → Option Bool) : ℕ := if ω 0 = some true then 1 else 3

lemma boundedTime_isStoppingTime :
    IsStoppingTime (pathFiltration (Option Bool))
      (fun ω : ℕ → Option Bool => (boundedTime ω : WithTop ℕ)) := by
  intro n
  have htime : Measurable[pathFiltration (Option Bool) n]
      (fun ω : ℕ → Option Bool => (boundedTime ω : WithTop ℕ)) :=
    (measurable_of_finite (fun s : Option Bool =>
      ((if s = some true then 1 else 3 : ℕ) : WithTop ℕ))).comp
      (eval_measurable n 0 (Nat.zero_le n))
  exact (measurableSet_Iic (a := (n : WithTop ℕ))).preimage htime

theorem boundedTime_one_mass : chain {ω | boundedTime ω = 1} = (1 / 2 : ℝ≥0∞) := by
  have heq : {ω : ℕ → Option Bool | boundedTime ω = 1} = {ω | ω 0 = some true} := by
    ext ω
    simp [boundedTime]
  rw [heq]
  simpa [initial, Measure.smul_apply, Measure.add_apply] using
    initial_event ({some true} : Set (Option Bool)) (measurableSet_singleton _)

theorem boundedTime_three_mass : chain {ω | boundedTime ω = 3} = (1 / 2 : ℝ≥0∞) := by
  have heq : {ω : ℕ → Option Bool | boundedTime ω = 3} = {ω | ω 0 ≠ some true} := by
    ext ω
    simp [boundedTime]
  rw [heq]
  simpa [initial, Measure.smul_apply, Measure.add_apply] using
    initial_event ({some true}ᶜ : Set (Option Bool)) (measurableSet_singleton _).compl

/-- The finite stopping-time interface is exercised at a nonconstant time and nonconstant functional. -/
theorem bounded_strong_markov :
    chain[(fun ω : ℕ → Option Bool =>
        timedCoordinate (boundedTime ω) (stoppedPathShift boundedTime ω)) |
        boundedTime_isStoppingTime.measurableSpace]
      =ᵐ[chain] fun ω =>
        markovExpectation (Option Bool) transition (timedCoordinate (boundedTime ω))
          (ω (boundedTime ω)) := by
  exact strong_markov_chain (Option Bool) initial transition boundedTime
    boundedTime_isStoppingTime timedCoordinate timedCoordinate_measurable
    ⟨1, timedCoordinate_bounded⟩

/-- The actual null initial-state event is nonempty as a set of paths. -/
theorem initial_none_null : chain {ω : ℕ → Option Bool | ω 0 = none} = 0 := by
  simpa [initial, Measure.smul_apply, Measure.add_apply] using
    initial_event ({none} : Set (Option Bool)) (measurableSet_singleton _)

/-- Infinity is used on that null event; elsewhere the two positive finite fibers are retained. -/
def almostFiniteTime (ω : ℕ → Option Bool) : WithTop ℕ :=
  if ω 0 = none then ⊤ else (boundedTime ω : WithTop ℕ)

lemma almostFiniteTime_isStoppingTime :
    IsStoppingTime (pathFiltration (Option Bool)) almostFiniteTime := by
  have hnull : MeasurableSet[pathFiltration (Option Bool) 0]
      {ω : ℕ → Option Bool | ω 0 = none} :=
    (measurableSet_singleton (none : Option Bool)).preimage (eval_measurable 0 0 le_rfl)
  intro n
  have heq : {ω : ℕ → Option Bool | almostFiniteTime ω ≤ (n : WithTop ℕ)} =
      {ω | ω 0 ≠ none} ∩ {ω | (boundedTime ω : WithTop ℕ) ≤ (n : WithTop ℕ)} := by
    ext ω
    by_cases hω : ω 0 = none <;> simp [almostFiniteTime, hω]
  change MeasurableSet[pathFiltration (Option Bool) n]
    {ω : ℕ → Option Bool | almostFiniteTime ω ≤ (n : WithTop ℕ)}
  rw [heq]
  exact ((pathFiltration (Option Bool)).mono (Nat.zero_le n) _ hnull).compl.inter
    (boundedTime_isStoppingTime n)

lemma almostFiniteTime_ae_finite : ∀ᵐ ω ∂chain, almostFiniteTime ω ≠ ⊤ := by
  rw [ae_iff]
  have heq : {ω : ℕ → Option Bool | ¬almostFiniteTime ω ≠ ⊤} = {ω | ω 0 = none} := by
    ext ω
    simp [almostFiniteTime]
  rw [heq]
  exact initial_none_null

theorem almostFiniteTime_infinite_path : almostFiniteTime (fun _ => (none : Option Bool)) = ⊤ :=
  rfl

/-- The a.s.-finite target is applied to an actual stopping time with infinity on a null set. -/
theorem almost_finite_strong_markov :
    chain[stoppedValue (fun n ω => timedCoordinate n (shiftPath n ω)) almostFiniteTime |
        almostFiniteTime_isStoppingTime.measurableSpace]
      =ᵐ[chain] stoppedValue
        (fun n ω => markovExpectation (Option Bool) transition (timedCoordinate n) (ω n))
        almostFiniteTime := by
  exact strong_markov_chain_ae_finite (Option Bool) initial transition almostFiniteTime
    almostFiniteTime_isStoppingTime almostFiniteTime_ae_finite timedCoordinate
    timedCoordinate_measurable ⟨1, timedCoordinate_bounded⟩

theorem infinite_path_observable_zero :
    stoppedValue (fun n ω => timedCoordinate n (shiftPath n ω)) almostFiniteTime
      (fun _ => (none : Option Bool)) = 0 := by
  simp [stoppedValue, timedCoordinate, shiftPath]

/-- Concrete alternating paths make the coordinate and shift index arithmetic observable. -/
def alternatingPath (b : Bool) : ℕ → Option Bool :=
  fun n => (fun s : Option Bool => s.map Bool.not)^[n] (some b)

theorem nonconstant_shift_computations :
    coordinateOne (shiftPath 1 (alternatingPath true)) = 1 ∧
    coordinateOne (shiftPath 1 (alternatingPath false)) = 0 := by
  constructor <;> rfl

theorem shift_zero_one_distinguished :
    coordinateOne (shiftPath 0 (alternatingPath true)) = 0 ∧
    coordinateOne (shiftPath 1 (alternatingPath true)) = 1 := by
  constructor <;> rfl

theorem nonconstant_stopping_computations :
    boundedTime (alternatingPath true) = 1 ∧
    boundedTime (alternatingPath false) = 3 ∧
    coordinateOne (stoppedPathShift boundedTime (alternatingPath true)) = 1 ∧
    coordinateOne (stoppedPathShift boundedTime (alternatingPath false)) = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem time_dependent_stopping_computations :
    timedCoordinate (boundedTime (alternatingPath true))
      (stoppedPathShift boundedTime (alternatingPath true)) = 1 ∧
    timedCoordinate (boundedTime (alternatingPath false))
      (stoppedPathShift boundedTime (alternatingPath false)) = (1 / 2 : ℝ) := by
  constructor
  · norm_num [timedCoordinate, coordinateOne, boundedTime, stoppedPathShift, alternatingPath]
  · norm_num [timedCoordinate, coordinateOne, boundedTime, stoppedPathShift, alternatingPath]

end FiniteState

#print axioms MathlibExt.Probability.MarkovPropertyChain.markov_property_full
#print axioms MathlibExt.Probability.MarkovPropertyChain.markov_setIntegral_shift
#print axioms MathlibExt.Probability.StrongMarkovChain.strong_markov_chain
#print axioms MathlibExt.Probability.MarkovChainPath.integral_shiftPath_traj_eq_markovExpectation

end MathlibExtTest.Probability.MarkovPropertyChain
