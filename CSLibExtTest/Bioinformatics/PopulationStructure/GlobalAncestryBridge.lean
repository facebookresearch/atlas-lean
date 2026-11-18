/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.PopulationStructure.GlobalAncestryBridge
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Tests for the global-ancestry f-statistics bridge

The examples restate the mixture identity, f4 linearity and rank bound, and
check the concrete two-source example and the one-source endpoint.
-/

namespace Cslib.Bioinformatics.PopulationStructure.AdmixtureEM

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.ADMIXTOOLS

variable {I J K : Type*} [Fintype K]

example (θ : Params I J K) (i : I) (j : J) :
    ancestryFreq θ (Sum.inl i) j = ∑ k, θ.Q i k * ancestryFreq θ (Sum.inr k) j :=
  ancestryFreq_inl_eq_sum θ i j

example {mJ : MeasurableSpace J} {μ : Measure J} (θ : Params I J K)
    (hp : ∀ X, MemLp (ancestryFreq θ X) 2 μ) (i : I) (X Y Z : I ⊕ K) :
    f4 μ (ancestryFreq θ) (Sum.inl i) X Y Z =
      ∑ k, θ.Q i k * f4 μ (ancestryFreq θ) (Sum.inr k) X Y Z :=
  f4_ancestryFreq_individual θ hp i X Y Z

example {mJ : MeasurableSpace J} {μ : Measure J} {n r k : ℕ}
    (θ : Params (Fin (n + 1)) J (Fin (k + 1)))
    (hp : ∀ X, MemLp (ancestryFreq θ X) 2 μ) (R : Fin (r + 1) → Fin (n + 1) ⊕ Fin (k + 1)) :
    (f4Matrix μ (ancestryFreq θ) Sum.inl R).rank ≤ k :=
  rank_f4Matrix_ancestryFreq_le θ hp R

/-- The concrete parameters of `probe.py`: three individuals, three loci,
two ancestral populations. -/
noncomputable def θex : Params (Fin 3) (Fin 3) (Fin 2) where
  Q := ![![1 / 2, 1 / 2], ![1 / 4, 3 / 4], ![3 / 4, 1 / 4]]
  F := ![![1 / 10, 1 / 2, 9 / 10], ![9 / 10, 1 / 2, 1 / 10]]
  Q_pos := by
    intro i k
    fin_cases i <;> fin_cases k <;> norm_num
  Q_sum := by
    intro i
    fin_cases i <;> norm_num [Fin.sum_univ_two]
  F_pos := by
    intro k j
    fin_cases k <;> fin_cases j <;> norm_num
  F_lt_one := by
    intro k j
    fin_cases k <;> fin_cases j <;> norm_num

/-- Acceptance: the individual-level f4 matrix of the example (individuals
on both sides, loci with the counting measure) has rank at most `K - 1 = 1`.
`probe.py` computes the matrix `[[2/25, -2/25], [-2/25, 2/25]]`, of rank
exactly `1`, so the bound is attained. -/
theorem rank_example_le_one :
    (f4Matrix (Measure.count : Measure (Fin 3)) (ancestryFreq θex) Sum.inl Sum.inl).rank ≤ 1 :=
  rank_f4Matrix_ancestryFreq_le_of_finite θex Sum.inl

/-- Endpoint `K = 1`: with one ancestral population the individual-level f4
matrix has rank `0` (all individuals have the same frequency `F`). -/
theorem rank_eq_zero_of_card_one {n r : ℕ} {J : Type*} [MeasurableSpace J] {μ : Measure J}
    (θ : Params (Fin (n + 1)) J (Fin 1))
    (hp : ∀ X, MemLp (ancestryFreq θ X) 2 μ) (R : Fin (r + 1) → Fin (n + 1) ⊕ Fin 1) :
    (f4Matrix μ (ancestryFreq θ) Sum.inl R).rank = 0 :=
  Nat.le_zero.mp (rank_f4Matrix_ancestryFreq_le θ hp R)

/-- Endpoint probe at the frequency level: in the example, individual `0`
has constant frequency `1/2` across loci (its two ancestral frequencies are
complementary), checked by evaluation of `qf`. -/
example (j : Fin 3) : ancestryFreq θex (Sum.inl 0) j = 1 / 2 := by
  have : ancestryFreq θex (Sum.inl 0) = qf θex 0 := rfl
  rw [this]
  fin_cases j <;> simp [qf, θex, Fin.sum_univ_two] <;> norm_num

end Cslib.Bioinformatics.PopulationStructure.AdmixtureEM
