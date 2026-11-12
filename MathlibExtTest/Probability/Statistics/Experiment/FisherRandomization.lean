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

end MathlibExtTest.Probability.Statistics.Experiment
