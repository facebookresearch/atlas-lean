/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Sampling.WithoutReplacement

@[expose] public section

open Finset

namespace MathlibExt.Probability.Sampling.WithoutReplacementTest

private def population : Finset (Fin 4) := Finset.univ

private def weights : Fin 4 → ℝ := ![0, 0, 1, 1]

private lemma weights_mem_Icc (i : Fin 4) : 0 ≤ weights i ∧ weights i ≤ 1 := by
  fin_cases i <;> norm_num [weights]

private def higherPopulation : Finset (ULift.{1} (Fin 4)) := Finset.univ

private def higherWeights (i : ULift.{1} (Fin 4)) : ℝ := weights i.down

private lemma higherWeights_mem_Icc (i : ULift.{1} (Fin 4)) :
    0 ≤ higherWeights i ∧ higherWeights i ≤ 1 := by
  exact weights_mem_Icc i.down

private lemma higherWeights_nonconstant :
    higherWeights (ULift.up 0) ≠ higherWeights (ULift.up 2) := by
  norm_num [higherWeights, weights]

private lemma higherPopulation_nonempty : higherPopulation.Nonempty := by
  exact ⟨ULift.up 0, by simp [higherPopulation]⟩

private lemma population_pairs :
    population.powersetCard 2 =
      ({{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}} : Finset (Finset (Fin 4))) := by
  decide

private lemma selected_pair_card :
    #({S ∈ ({{2, 3}} : Finset (Finset (Fin 4))) |
        2 ≤ ∑ i ∈ S, weights i}) = 1 := by
  rw [filter_eq_self.2]
  · decide
  · intro S hS
    simp only [mem_singleton] at hS
    subst S
    norm_num [weights]

private lemma inclusive_tail_card :
    #{S ∈ population.powersetCard 2 |
        2 * ((∑ i ∈ population, weights i) / #population) + (1 / 2 : ℝ) * 2 * 1 ≤
          ∑ i ∈ S, weights i} = 1 := by
  rw [population_pairs]
  norm_num [Finset.filter_insert, Finset.card_insert_of_notMem, population, weights,
    Fin.sum_univ_succ]
  exact selected_pair_card

/-- The inclusive threshold is attained only by the pair of the two weight-one elements. -/
example :
    #{S ∈ population.powersetCard 2 |
        2 * ((∑ i ∈ population, weights i) / #population) + (1 / 2 : ℝ) * 2 * 1 ≤
          ∑ i ∈ S, weights i} = 1 := by
  exact inclusive_tail_card

/-- The populated four-element example gives the genuine bound `1 ≤ 6 * exp (-1)`. -/
example : (1 : ℝ) ≤ 6 * Real.exp (-1) := by
  have h := Finset.card_sample_tail_le population weights (R := 1) (t := 1 / 2)
    (by norm_num) (fun i _ ↦ weights_mem_Icc i) (by simp [population]) 2 (by norm_num)
  rw [population_pairs] at h
  norm_num [Finset.filter_insert, Finset.card_insert_of_notMem,
    population, weights, Fin.sum_univ_succ, Nat.choose] at h
  have hcard :
      #({S ∈ ({{2, 3}} : Finset (Finset (Fin 4))) |
          (2 : ℝ) ≤ ∑ i ∈ S, ![(0 : ℝ), 0, 1, 1] i}) = 1 := by
    rw [filter_eq_self.2]
    · decide
    · intro S hS
      simp only [mem_singleton] at hS
      subst S
      norm_num
  rw [hcard] at h
  simpa [mul_comm] using h

/-- The public bound applies to a populated finite type in a higher universe. -/
example :
    (#{S ∈ higherPopulation.powersetCard 2 |
        2 * ((∑ i ∈ higherPopulation, higherWeights i) / #higherPopulation) +
          (1 / 2 : ℝ) * 2 * 1 ≤ ∑ i ∈ S, higherWeights i} : ℝ) ≤
      Real.exp (-(2 * 2 * (1 / 2 : ℝ) ^ 2)) * (#higherPopulation).choose 2 := by
  exact Finset.card_sample_tail_le (ι := ULift.{1} (Fin 4)) higherPopulation higherWeights
    (R := 1) (t := 1 / 2) (by norm_num) (fun i _ ↦ higherWeights_mem_Icc i)
    higherPopulation_nonempty 2 (by norm_num)

/-- At `t = 0`, constant weights select every two-element subset. -/
example :
    #{S ∈ population.powersetCard 2 |
        2 * ((∑ _i ∈ population, (0 : ℝ)) / #population) + 0 * 2 * 1 ≤
          ∑ _i ∈ S, (0 : ℝ)} = 6 := by
  rw [population_pairs]
  norm_num [Finset.filter_insert, Finset.card_insert_of_notMem]
  decide

/-- At `t = 1`, the populated example has an empty upper tail. -/
example :
    #{S ∈ population.powersetCard 2 |
        2 * ((∑ i ∈ population, weights i) / #population) + 1 * 2 * 1 ≤
          ∑ i ∈ S, weights i} = 0 := by
  rw [population_pairs]
  norm_num [Finset.filter_insert, Finset.card_insert_of_notMem, population, weights,
    Fin.sum_univ_succ]

/-- Sampling zero elements leaves the unique empty sample in the non-strict tail at `t = 0`. -/
example :
    #{S ∈ population.powersetCard 0 |
        0 * ((∑ i ∈ population, weights i) / #population) + 0 * 0 * 1 ≤
          ∑ i ∈ S, weights i} = 1 := by
  rw [powersetCard_zero]
  simp
  rw [filter_eq_self.2]
  · decide
  · intro S hS
    simp only [mem_singleton] at hS
    subst S
    simp

/-- Sampling more elements than the population contains gives an empty family. -/
example :
    #{S ∈ population.powersetCard 5 |
        5 * ((∑ i ∈ population, weights i) / #population) + 0 * 5 * 1 ≤
          ∑ i ∈ S, weights i} = 0 := by
  norm_num [population, weights, Finset.powersetCard]

/-- Strict positivity of `R` is necessary: at `R = 0`, every zero-weight singleton is selected
while the proposed positive-deviation bound is strictly smaller than the number of singletons. -/
example : ¬(
    (#{S ∈ population.powersetCard 1 |
        1 * ((∑ _i ∈ population, (0 : ℝ)) / #population) + 1 * 1 * 0 ≤
          ∑ _i ∈ S, (0 : ℝ)} : ℝ) ≤
      Real.exp (-(2 * 1 * (1 : ℝ) ^ 2)) * (#population).choose 1) := by
  norm_num [population, Finset.powersetCard]

/-- The theorem exposes no hidden `n ≤ #s` or `0 < n` premise. -/
example (n : ℕ) :
    (#{S ∈ population.powersetCard n |
        n * ((∑ i ∈ population, weights i) / #population) ≤ ∑ i ∈ S, weights i} : ℝ) ≤
      Real.exp (-(2 * n * (0 : ℝ) ^ 2)) * (#population).choose n := by
  simpa using Finset.card_sample_tail_le population weights (R := 1) (t := 0)
    (by norm_num) (fun i _ ↦ weights_mem_Icc i) (by simp [population]) n (by norm_num)

#print axioms Finset.card_sample_tail_le

end MathlibExt.Probability.Sampling.WithoutReplacementTest
