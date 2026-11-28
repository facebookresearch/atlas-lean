/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.LatticeMengerAttachData

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.LatticeMengerAttachData`

* `lmg_corridors_disjoint` for the three axes of `ℤ³`: pairwise disjoint corridors avoiding the
  origin (instance).
* `lmg_disjointRouting_of_assignment` and `lmg_axisAssignment_of_candidates` as conditional
  statements.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.LatticeMengerAttachData

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

-- The three axis corridors of `ℤ³` are pairwise disjoint and avoid the origin.
example : Disjoint (lma_corridorVerts (0 : Fin 3) 5) (lma_corridorVerts 2 5) ∧
    (0 : Site 3) ∉ lma_corridorVerts 1 5 :=
  ⟨(lmg_corridors_disjoint (j₁ := 0) (j₂ := 1) (j₃ := 2) (by decide) (by decide) (by decide)
      5).1.2.1,
    (lmg_corridors_disjoint (j₁ := 0) (j₂ := 1) (j₃ := 2) (by decide) (by decide) (by decide)
      5).2.2.1⟩

-- An axis assignment gives disjoint routing.
example (n : ℕ) (h : lmg_BoxAxisAssignment 3 n) : hrHD_DisjointRouting 3 n :=
  lmg_disjointRouting_of_assignment h

-- Candidate axes give an axis assignment.
example (ω : ConfigSpace (Sym2 (Site 3))) (x₁ x₂ x₃ : Site 3) (S : Fin 3 → Finset (Fin 3))
    (h : caa_RunsAlongCandidates ω ![x₁, x₂, x₃] S) :
    ∃ j₁ j₂ j₃ : Fin 3, (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
      crr_AxisAssignment ω x₁ j₁ ∧ crr_AxisAssignment ω x₂ j₂ ∧ crr_AxisAssignment ω x₃ j₃ :=
  lmg_axisAssignment_of_candidates ω x₁ x₂ x₃ S h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.LatticeMengerAttachData
