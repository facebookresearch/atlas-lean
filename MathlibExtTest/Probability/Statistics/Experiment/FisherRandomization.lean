/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Experiment.FisherRandomization
public import MathlibExt.Probability.Causality.CausalIdentification

/-!
# Tests for Fisher randomization validity

Sharp-null use case, level `0` and level `1` boundaries, and the degenerate
beyond-population law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
open MathlibExt.Probability.Causality MathlibExt.Probability.Statistics.Experiment
open MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.Experiment

open MeasureTheory ProbabilityTheory Finset
open MathlibExt.Probability.Causality MathlibExt.Probability.Statistics.Experiment
open MathlibExt.Probability.Statistics.MultipleTesting

/-- Use case (sharp null): the permutation p-value of `diffInMeans y₀ y₀`
is valid under complete randomization. -/
example (y₀ : Fin 4 → ℝ) : IsValidPValue (completeRandomization (Fin 4) 2)
    (permutationPValue (Equiv.Perm (Fin 4)) (diffInMeans y₀ y₀)) := by
  exact isValidPValue_fisherRandomization (by decide) Measurable.of_discrete

/-- Boundary `α = 0`: the rejection event at level `0` has measure zero.
The set-builder predicate compares reals (`≤ 0`); the measure bound is the
`IsValidPValue` conclusion at `t = 0`. -/
example (y₀ : Fin 4 → ℝ) : (completeRandomization (Fin 4) 2)
    {S | permutationPValue (Equiv.Perm (Fin 4)) (diffInMeans y₀ y₀) S ≤ 0} ≤
      ENNReal.ofReal 0 := by
  have hvalid : IsValidPValue (completeRandomization (Fin 4) 2)
      (permutationPValue (Equiv.Perm (Fin 4)) (diffInMeans y₀ y₀)) :=
    isValidPValue_fisherRandomization (by decide)
      Measurable.of_discrete
  exact hvalid 0 ⟨le_rfl, zero_le_one⟩

/-- Boundary `α = 1`: every p-value is at most `1`, so the rejection event
at level `1` is the whole space. This states set equality to `univ`, which
guards `permutationPValue ≤ 1`; the mere measure bound `≤ ofReal 1` is a
trivial probability bound and is not used. -/
example (y₀ : Fin 4 → ℝ) :
    {S | permutationPValue (Equiv.Perm (Fin 4)) (diffInMeans y₀ y₀) S ≤ 1} =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro S
  show permutationPValue (Equiv.Perm (Fin 4)) (diffInMeans y₀ y₀) S ≤ 1
  have hpos : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin 4)) := by
    exact_mod_cast Fintype.card_pos
  rw [permutationPValue, div_le_one hpos]
  exact_mod_cast Finset.card_filter_le _ _

/-- Degenerate law: beyond the population size the assignment law is the zero
measure, so validity is not claimed there. -/
example : completeRandomization (Fin 4) 5 = 0 := by
  rw [completeRandomization_eq, Measure.uniformOfFinset,
    powersetCard_eq_empty.2 (by simp), sum_empty]

/-- Heterogeneous-effect fixture: equal means, pointwise different effects. -/
noncomputable def sepY₀ : Fin 4 → ℝ := ![0, 0, 1, 1]

noncomputable def sepY₁ : Fin 4 → ℝ := ![0, 1, 0, 1]

/-- The fixture has zero average effect. -/
example : ate sepY₀ sepY₁ = 0 := by
  simp only [ate, popMean, Fin.sum_univ_four]
  norm_num [sepY₀, sepY₁]

/-- ... but the sharp null fails pointwise. -/
example : ∃ i, sepY₁ i ≠ sepY₀ i := by
  exact ⟨1, by simp [sepY₁, sepY₀]⟩

/-- ... and the observed statistic is genuinely random over assignments. -/
example : ∃ S₁ S₂ : Finset (Fin 4), S₁.card = 2 ∧ S₂.card = 2 ∧
    diffInMeans sepY₀ sepY₁ S₁ ≠ diffInMeans sepY₀ sepY₁ S₂ := by
  have c1 : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
  have c2 : ({2, 3} : Finset (Fin 4))ᶜ = {0, 1} := by decide
  have p01 : (0 : Fin 4) ≠ 1 := by decide
  have p23 : (2 : Fin 4) ≠ 3 := by decide
  refine ⟨{0, 1}, {2, 3}, by decide, by decide, ?_⟩
  simp only [diffInMeans, sampleMean, c1, c2, Finset.sum_pair p01, Finset.sum_pair p23,
    Finset.card_pair p01, Finset.card_pair p23]
  norm_num [sepY₀, sepY₁]

/-- Sharp-null validity uses a single imputed schedule: under the sharp null
the observable statistic is `diffInMeans y₀ y₀` for the one observed schedule,
here instantiated at `y₀ := sepY₀`. This is the sharp-null validity claim
proper, distinct from the weak-null failure documented above (`ate sepY₀ sepY₁
= 0` holds while `sepY₁ ≠ sepY₀` pointwise): the oracle statistic
`diffInMeans sepY₀ sepY₁` mixes two schedules and is not imputable from one
realized assignment under the weak null alone (where `y₁ ≠ y₀`, no single
schedule reproduces both arms), so validity for it would say nothing about
sharp-versus-weak null behavior. Under the sharp null itself each unit's
observed outcome imputes its missing potential outcome, so the whole
reassignment statistic is identified with `diffInMeans y₀ y₀`. -/
example : IsValidPValue (completeRandomization (Fin 4) 2)
      (permutationPValue (Equiv.Perm (Fin 4)) (diffInMeans sepY₀ sepY₀)) := by
  exact isValidPValue_fisherRandomization (by decide) Measurable.of_discrete

/-- Degenerate case: with `y₁ = y₀` both the weak and the sharp null hold. -/
example (y₀ : Fin 4 → ℝ) : ate y₀ y₀ = 0 ∧ ∀ i, y₀ i = y₀ i := by
  refine ⟨?_, fun i => rfl⟩
  simp [ate, popMean]

end MathlibExtTest.Probability.Statistics.Experiment