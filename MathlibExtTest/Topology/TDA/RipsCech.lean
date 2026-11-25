/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.TDA.RipsCech

@[expose] public section

open MathlibExt.Topology.TDA

/-- Two points at distance one span an edge of the Rips complex at scale one. -/
example : ({0, 1} : Finset ℝ) ∈ (ripsComplex 1 : PreAbstractSimplicialComplex ℝ) := by
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  simp [Real.dist_eq]

/-- At scale one, the Čech complex of the line contains the edge `{0, 2}` (centre `1`) but the
Rips complex does not: the inclusions of Prop. 2.6 need the factor `2`. -/
example : ({0, 2} : Finset ℝ) ∈ (cechComplex 1 : PreAbstractSimplicialComplex ℝ) ∧
    ({0, 2} : Finset ℝ) ∉ (ripsComplex 1 : PreAbstractSimplicialComplex ℝ) := by
  refine ⟨⟨Finset.insert_nonempty _ _, 1, ?_⟩, fun h => ?_⟩
  · simp [Real.dist_eq]
    norm_num [abs_of_nonneg, abs_of_neg]
  · have := h.2 0 (by simp) 2 (by simp)
    norm_num [Real.dist_eq] at this

example (ε : ℝ) : (cechComplex ε : PreAbstractSimplicialComplex ℝ) ≤ cechComplex (2 * ε) :=
  (cechComplex_le_ripsComplex_le_cechComplex ε).1.trans
    (cechComplex_le_ripsComplex_le_cechComplex ε).2

example : ({0, 1} : Finset ℝ).Nonempty ∧ (ripsGraph 1).IsClique (({0, 1} : Finset ℝ) : Set ℝ) :=
  (mem_ripsComplex_iff_isClique zero_le_one).1 ⟨Finset.insert_nonempty _ _, by simp [Real.dist_eq]⟩
