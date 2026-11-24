/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Ported from fairinternal/formal-math `MathlibExtTest/Geometry/Metric.lean`
at commit 5971cd008f11196e18b863495ddad4501d3e5585.
The test statements and proofs are retained; only the Atlas adapter
import prefix is removed for the native ATLAS module identities.
-/

module

public import MathlibExt.Geometry.Metric
public import Mathlib.Topology.Instances.Real.Lemmas

namespace MetaMathlibExt

-- Compile-time use: `minimalDistinctDistances` takes an explicit existence witness
-- for a one-point `Finset` in `ℝ`, so the candidate set is never silently empty.
noncomputable example : ℕ := minimalDistinctDistances ℝ 1 ⟨{0}, by simp⟩

example : distanceMultiplicity ({0} : Finset ℝ) 0 = 0 := by
  simp [distanceMultiplicity]

example : distanceSet ({0} : Finset ℝ) = ∅ := by
  simp [distanceSet]

private lemma offDiag_zero_one :
    ({0, 1} : Finset ℝ).offDiag = {(0, 1), (1, 0)} := by
  ext ⟨x, y⟩
  simp only [Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  aesop

private lemma filter_distance_one_zero_one :
    ({pair ∈ ({((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (0 : ℝ))} : Finset (ℝ × ℝ)) |
      dist pair.1 pair.2 = 1}) = {((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (0 : ℝ))} := by
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · exact fun h ↦ h.1
  · intro h
    refine ⟨h, ?_⟩
    rcases h with h | h
    · obtain ⟨rfl, rfl⟩ := h
      norm_num [Real.dist_eq]
    · obtain ⟨rfl, rfl⟩ := h
      norm_num [Real.dist_eq]

example : distanceMultiplicity ({0, 1} : Finset ℝ) 1 = 1 := by
  rw [distanceMultiplicity, offDiag_zero_one, filter_distance_one_zero_one]
  norm_num

example : unitDistNum ({0, 1} : Finset ℝ) = 1 := by
  rw [unitDistNum, distanceMultiplicity, offDiag_zero_one, filter_distance_one_zero_one]
  norm_num

example : distanceSet ({0, 1, 2} : Finset ℝ) = {1, 2} := by
  norm_num [distanceSet, Finset.offDiag_insert, Finset.filter_insert, Real.dist_eq]

example : distinctDistances ({0, 1, 2} : Finset ℝ) = 2 := by
  norm_num [distinctDistances, distanceSet, Finset.offDiag_insert, Finset.filter_insert,
    Real.dist_eq]

example : distinctDistancesFrom ({0, 1, 2} : Finset ℝ) 0 = 2 := by
  norm_num [distinctDistancesFrom, Real.dist_eq]

end MetaMathlibExt
