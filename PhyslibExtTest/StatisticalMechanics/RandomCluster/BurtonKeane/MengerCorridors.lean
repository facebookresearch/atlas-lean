/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerCorridors

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerCorridors`

* `mco_exists_three_disjoint_corridors` in `ℤ³` with the all-closed configuration and `L = 2`:
  three disjoint opened corridors avoiding the origin (instance).
* `mco_corridorVerts_disjoint` for the axes `e₀`, `e₂` of `ℤ³`.
* `mco_mergeFree_of_reach` as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerCorridors

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

-- Three disjoint corridors along distinct axes.
example : ∃ (j₁ j₂ j₃ : Fin 3) (C₁ C₂ C₃ : Set (Site 3)), (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
    (Disjoint C₁ C₂ ∧ Disjoint C₁ C₃ ∧ Disjoint C₂ C₃) := by
  obtain ⟨j₁, j₂, j₃, C₁, C₂, C₃, hj, -, -, -, hdisj, -⟩ :=
    mco_exists_three_disjoint_corridors (fun _ => false) le_rfl 2 (by norm_num)
  exact ⟨j₁, j₂, j₃, C₁, C₂, C₃, hj, hdisj⟩

-- Corridors along `e₀` and `e₂` are disjoint.
example : Disjoint (mco_corridorVerts (0 : Fin 3) 3) (mco_corridorVerts 2 3) :=
  mco_corridorVerts_disjoint (by decide) 3

-- Three clusters reaching the origin give the merge-free condition.
example (ω : ConfigSpace (Sym2 (Site 3))) (h : mco_ThreeClustersReachOrigin ω) :
    bka_MergeFree ω := by
  obtain ⟨a₁, a₂, a₃, x₁, x₂, x₃, hadj, hconn, hinf, hdist⟩ := h
  exact mco_mergeFree_of_reach ω a₁ a₂ a₃ x₁ x₂ x₃ hadj hconn hinf hdist

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerCorridors
