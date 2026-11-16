/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Admixture.F3LineageIdentity
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory
open MathlibExt.Biology.PopulationGenetics.FStatistics
open scoped ENNReal symmDiff

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.F3LineageIdentity

/-- Termwise binary cases, including the two configurations contributing `1`. -/
example :
    ((1 : ℝ) - 0) * (1 - 0) = 1 ∧ ((0 : ℝ) - 1) * (0 - 1) = 1 ∧
      ((1 : ℝ) - 1) * (1 - 0) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [MathlibExt.Biology.PopulationGenetics.Admixture.mul_sub_mul_sub_of_binary]
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      all_goals norm_num

/-- The uniform probability measure on `Fin 4`. -/
noncomputable def μ4 : Measure (Fin 4) := (4⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ4 :=
  ⟨by simpa [μ4] using ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

/-- Integration against `μ4` is averaging over the four outcomes. -/
theorem integral_μ4 (f : Fin 4 → ℝ) : ∫ ω, f ω ∂μ4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  simp only [μ4, integral_smul_measure, integral_count, Fin.sum_univ_four]
  norm_num
  ring

/-- Two orthogonal drift increments, each with second moment `1/16`. -/
noncomputable def incr4 : Fin 2 → Fin 4 → ℝ :=
  ![![1 / 4, 1 / 4, -1 / 4, -1 / 4], ![1 / 4, -1 / 4, 1 / 4, -1 / 4]]

/-- Binary-loading witness: population `0` traverses both edges, while
populations `1` and `2` traverse neither. -/
noncomputable def M : DriftModel μ4 (Fin 2) (Fin 3) where
  root := fun _ => 1 / 2
  incr := incr4
  len := fun _ => 1 / 16
  weight := ![![1, 1], ![0, 0], ![0, 0]]
  memLp_root := MemLp.of_discrete
  memLp_incr := fun _ => MemLp.of_discrete
  inner_incr := by
    intro e f h
    fin_cases e <;> fin_cases f <;> simp_all [integral_μ4, incr4] <;> norm_num
  sq_incr := by
    intro e
    fin_cases e <;> simp [integral_μ4, incr4] <;> norm_num

theorem M_hasBinaryLoadings : M.HasBinaryLoadings := by
  intro X e
  fin_cases X <;> fin_cases e <;> simp [M]

/-- The lineage identity applies to the witness. -/
example :
    f3 μ4 M.freq 0 1 2 =
      ∑ e ∈ (M.lineage 0 ∆ M.lineage 1) ∩ (M.lineage 0 ∆ M.lineage 2), M.len e :=
  M.f3_eq_sum_inter_symmDiff M_hasBinaryLoadings 0 1 2

/-- Both edges contribute, so the value is `1/16 + 1/16 = 1/8`. -/
example : f3 μ4 M.freq 0 1 2 = 1 / 8 := by
  rw [M.f3_freq]
  simp [M, Fin.sum_univ_two]
  norm_num

end MathlibExtTest.Biology.PopulationGenetics.Admixture.F3LineageIdentity
