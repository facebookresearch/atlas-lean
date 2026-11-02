/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.RightStep
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.RightStep`

* `ecc_RightStep` holds for the one-vertex closed walk at the origin (through
  `ecc_rightStep_of_rightDodge`), so `ecc_reaches_right_band` is nonvacuous: every outside off-walk
  site reaches column `R + 1` off the walk.
* `RightStepCounterexample` shows the property can fail for other walks.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.RightStep

/-- The right-step property for the one-vertex closed walk at the origin. -/
theorem rightStep_nil (R : ℕ) :
    ecc_RightStep (Walk.nil : (hypercubicLattice 2).Walk ![0, 0] ![0, 0]) R := by
  apply ecc_rightStep_of_rightDodge
  intro z _ hzoff _ hnb
  simp only [Walk.support_nil, List.mem_singleton] at hnb hzoff
  have h0 : z 0 = -1 := by have := congrFun hnb 0; simp at this; omega
  have h1 : z 1 = 0 := by have := congrFun hnb 1; simpa using this
  have hz : z = ![-1, 0] := by ext i; fin_cases i <;> simp [h0, h1]
  subst hz
  refine ⟨![0, 1], by simp, ?_⟩
  have hA : (offSupport (Walk.nil : (hypercubicLattice 2).Walk ![0, 0] ![0, 0])).Adj
      ![-1, 0] ![-1, 1] := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide
    · simp only [Walk.support_nil, List.mem_singleton]; decide
    · simp only [Walk.support_nil, List.mem_singleton]; decide
  have hB : (offSupport (Walk.nil : (hypercubicLattice 2).Walk ![0, 0] ![0, 0])).Adj
      ![-1, 1] ![0, 1] := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide
    · simp only [Walk.support_nil, List.mem_singleton]; decide
    · simp only [Walk.support_nil, List.mem_singleton]; decide
  exact hA.reachable.trans hB.reachable

/-- The one-vertex closed walk at the origin. -/
abbrev W0 : (hypercubicLattice 2).Walk ![0, 0] ![0, 0] := Walk.nil

example (z : Site 2) (hzout : z ∉ jec_leftRegion W0) (hzoff : z ∉ W0.support) :
    ∃ w : Site 2, ((3 : ℕ) : ℤ) + 1 ≤ w 0 ∧ (offSupport W0).Reachable z w :=
  ecc_reaches_right_band _ 3 (rightStep_nil 3) z hzout hzoff

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.RightStep
