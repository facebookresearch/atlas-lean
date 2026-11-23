/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.TildePc

/-!
# Tests for `MathlibExt.Probability.Percolation.TildePc`

Tests the definitions `StatMech.Percolation.coordShift`, `stepSign`, `boundaryEdges`,
`connWithinProb`, `phi`, `tildePcSet` and `tildePc`: unit steps at the origin, `∂∅ = ∅` and
`φ_p(∅) = 0`, `connWithinProb = 0` off `S`, `φ_0(S) = 0`, hence `0 ∈ tildePcSet d` with witness
`S = {0}` and `0 ≤ p̃_c(d) ≤ 1`.
-/

@[expose] public section

open StatMech StatMech.Percolation StatMech.Lattice
open scoped NNReal

namespace MathlibExtTest.StatMech.Probability.Percolation.TildePc

-- Unit steps.
example : stepSign true = 1 ∧ stepSign false = -1 := ⟨rfl, rfl⟩

example : coordShift (origin 2) 0 (stepSign true) 0 = 1 := by
  simp [coordShift, stepSign, origin]

example : coordShift (origin 2) 0 (stepSign false) 1 = 0 := by
  simp [coordShift, stepSign, origin]

-- The empty set has empty boundary and `φ_p(∅) = 0`.
example (d : ℕ) : boundaryEdges d ∅ = ∅ := by simp [boundaryEdges]

example (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : phi d p hp ∅ = 0 := by
  simp [phi, boundaryEdges]

-- `ℙ_p(0 ↔ x inside S) = 0` when `x ∉ S`.
example (p : ℝ≥0) (hp : p ≤ 1) :
    connWithinProb 2 p hp {origin 2} (fun _ => 1) = 0 := by
  have hx : (fun _ => (1 : ℤ)) ∉ ({origin 2} : Finset (Site 2)) := by
    simp only [Finset.mem_singleton]
    intro h
    have := congrFun h 0
    simp [origin] at this
  simp [connWithinProb, hx]

-- `φ_0(S) = 0`, so `0 ∈ tildePcSet d` with witness `S = {0}`.
theorem zero_mem_tildePcSet (d : ℕ) : (0 : ℝ≥0) ∈ tildePcSet d :=
  ⟨zero_le_one, {origin d}, Finset.mem_singleton_self _, by simp [phi]⟩

-- `0 ≤ p̃_c(d) ≤ 1`, and `φ` is nonnegative.
example (d : ℕ) : tildePc d ≤ 1 :=
  csSup_le ⟨0, zero_mem_tildePcSet d⟩ fun _ hq => (mem_tildePcSet.mp hq).1

example (p : ℝ≥0) (hp : p ≤ 1) : 0 ≤ phi 2 p hp {origin 2} := phi_nonneg _ _ _ _

end MathlibExtTest.StatMech.Probability.Percolation.TildePc
