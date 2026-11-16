/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatistics
import Mathlib.Tactic.NormNum

/-!
# The `f3` lineage identity for binary loadings

For binary lineage weights, the `f3` summand on an edge is the indicator that
the target population's weight differs from both source weights. Summing over
edges gives

`f3(C; A, B) = ∑ e ∈ (lineage C ∆ lineage A) ∩ (lineage C ∆ lineage B), len e`.

On a tree the lineage sets are root-to-population paths, so this is the
drift length of the path from `C` to the `A`–`B` path. This identity is the
exact form behind the existing nonnegativity theorem
`DriftModel.f3_nonneg_of_hasBinaryLoadings`.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Admixture

/-- Termwise form of the `f3` summand for binary weights: when all three
weights are `0` or `1`, `(wC - wA) * (wC - wB)` is `1` exactly when `wC`
differs from both `wA` and `wB`, and `0` otherwise. -/
theorem mul_sub_mul_sub_of_binary {wC wA wB : ℝ}
    (hC : wC = 0 ∨ wC = 1) (hA : wA = 0 ∨ wA = 1) (hB : wB = 0 ∨ wB = 1) :
    (wC - wA) * (wC - wB) = if wC ≠ wA ∧ wC ≠ wB then 1 else 0 := by
  rcases hC with rfl | rfl <;> rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> norm_num

end MathlibExt.Biology.PopulationGenetics.Admixture

namespace MathlibExt.Biology.PopulationGenetics.FStatistics

open MeasureTheory
open scoped symmDiff

/-- With binary loadings, `f3 C A B` is the total drift length of the edges
lying in both symmetric differences `lineage C ∆ lineage A` and
`lineage C ∆ lineage B`. On a tree this is the path length from `C` to the
`A`–`B` path. -/
theorem DriftModel.f3_eq_sum_inter_symmDiff {Ω P E : Type*}
    {m : MeasurableSpace Ω} {μ : Measure Ω} [Fintype E] [DecidableEq E]
    (M : DriftModel μ E P) (hM : M.HasBinaryLoadings) (C A B : P) :
    f3 μ M.freq C A B =
      ∑ e ∈ (M.lineage C ∆ M.lineage A) ∩ (M.lineage C ∆ M.lineage B), M.len e := by
  rw [M.f3_freq,
    ← Finset.univ_inter ((M.lineage C ∆ M.lineage A) ∩
      (M.lineage C ∆ M.lineage B)),
    ← Finset.sum_ite_mem]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MathlibExt.Biology.PopulationGenetics.Admixture.mul_sub_mul_sub_of_binary
    (hM C e) (hM A e) (hM B e)]
  rcases hM C e with hC | hC <;> rcases hM A e with hA | hA <;>
    rcases hM B e with hB | hB <;>
    simp [DriftModel.lineage, Finset.mem_inter, Finset.mem_symmDiff, hC, hA, hB]

end MathlibExt.Biology.PopulationGenetics.FStatistics
