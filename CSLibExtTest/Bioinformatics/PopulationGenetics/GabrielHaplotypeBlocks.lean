/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Bioinformatics.PopulationGenetics.GabrielHaplotypeBlocks
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace CSLibExtTest.Bioinformatics.PopulationGenetics.GabrielHaplotypeBlocks

open Cslib.Bioinformatics.PopulationGenetics.GabrielHaplotypeBlocks

private def ld : NonemptyInterval ℝ := ⟨⟨0.7, 0.98⟩, by norm_num⟩
private def ehr : NonemptyInterval ℝ := ⟨⟨0.7, 0.89⟩, by norm_num⟩
private def neutral : NonemptyInterval ℝ := ⟨⟨0.7, 0.9⟩, by norm_num⟩

example : classify ld = .strongLD := by norm_num [classify, ld]
example : classify ehr = .strongEHR := by norm_num [classify, ehr]
example : classify neutral = .nonInformative := by norm_num [classify, neutral]
example : classify ⟨⟨0.69, 0.98⟩, by norm_num⟩ = .nonInformative := by norm_num [classify]
example : classify ⟨⟨0.7, 0.97⟩, by norm_num⟩ = .nonInformative := by norm_num [classify]

private def intervals (u v : Fin 4) : NonemptyInterval ℝ :=
  if u = 1 ∧ v = 2 then ehr else if u = 2 ∧ v = 3 then neutral else ld

private theorem pairs_eq : regionPairs (1 : Fin 4) 3 = {(1, 2), (1, 3), (2, 3)} := by
  ext ⟨u, v⟩
  fin_cases u <;> fin_cases v <;> decide

-- The three in-region pairs have one of each kind. The non-informative pair is not
-- in the denominator, and index 0 is outside the region.
example : pairCount intervals 1 3 .strongLD = 1 ∧ pairCount intervals 1 3 .strongEHR = 1 := by
  simp only [pairCount, pairs_eq, Finset.filter_insert, Finset.filter_singleton]
  norm_num [intervals, classify, ld, ehr, neutral]

example : regionWeight intervals (1 / 2) 1 3 = 0 := by
  norm_num [regionWeight, pairs_eq, intervals, classify, ld, ehr, neutral, pairWeight]

example : IsHaplotypeBlock intervals (1 / 2) 1 3 := by
  rw [isHaplotypeBlock_iff_regionWeight intervals (by norm_num [Set.mem_Ioo]) (by decide)]
  norm_num [regionWeight, pairs_eq, intervals, classify, ld, ehr, neutral, pairWeight]

example : ¬ IsHaplotypeBlock intervals (3 / 4) 1 3 := by
  rw [isHaplotypeBlock_iff_regionWeight intervals (by norm_num [Set.mem_Ioo]) (by decide)]
  norm_num [regionWeight, pairs_eq, intervals, classify, ld, ehr, neutral, pairWeight]

-- A nonnegative region weight does not replace the outer-pair test.
example : ¬ IsHaplotypeBlock intervals (1 / 2) 2 3 := by
  norm_num [IsHaplotypeBlock, intervals, classify, neutral]

-- At d = 1, even a non-informative outer pair can pass the weight tests.
example : ¬ IsHaplotypeBlock intervals 1 2 3 ∧
    pairWeight 1 (classify (intervals 2 3)) = 1 - 1 ∧ 0 ≤ regionWeight intervals 1 2 3 := by
  have hpairs : regionPairs (2 : Fin 4) 3 = {(2, 3)} := by
    ext ⟨u, v⟩
    fin_cases u <;> fin_cases v <;> decide
  norm_num [IsHaplotypeBlock, regionWeight, hpairs, intervals, classify, neutral, pairWeight]

-- With i = j, a diagonal interval is not an outer pair, even if it passes the LD cutoffs.
example : ¬ IsHaplotypeBlock (fun (_ _ : Fin 1) => ld) (1 / 2) 0 0 ∧
    pairWeight (1 / 2) (classify ld) = 1 - 1 / 2 ∧
    0 ≤ regionWeight (fun (_ _ : Fin 1) => ld) (1 / 2) 0 0 := by
  norm_num [IsHaplotypeBlock, regionWeight, regionPairs, classify, ld, pairWeight]

end CSLibExtTest.Bioinformatics.PopulationGenetics.GabrielHaplotypeBlocks
