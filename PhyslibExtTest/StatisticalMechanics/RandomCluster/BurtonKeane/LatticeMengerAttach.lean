/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.LatticeMengerAttach

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.LatticeMengerAttach`

* `lma_corridorVerts_disjoint`: in `ℤ³` the corridors along `e₀` and `e₁` are disjoint
  (instance), while `2 e₀` lies on the `e₀` corridor of length `2`.
* `lma_disjointRouting_of_reachesRay` and `lma_attachData_of_three_reachesRay` as conditional
  statements.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.LatticeMengerAttach

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

-- Corridors along distinct axes are disjoint.
example : Disjoint (lma_corridorVerts (0 : Fin 3) 4) (lma_corridorVerts 1 4) :=
  lma_corridorVerts_disjoint (by decide) 4

-- The point `2 e₀` lies on the corridor along `e₀`.
example : hrHD_rayPt (0 : Fin 3) 2 ∈ lma_corridorVerts 0 2 :=
  ⟨2, by norm_num, by norm_num, rfl⟩

-- The box ray condition gives disjoint routing.
example (n : ℕ) (h : lma_BoxClusterReachesRay 3 n) : hrHD_DisjointRouting 3 n :=
  lma_disjointRouting_of_reachesRay h

-- Three corridor clusters give attachment data.
example (ω : ConfigSpace (Sym2 (Site 3))) (x₁ x₂ x₃ : Site 3) (j₁ j₂ j₃ : Fin 3)
    (h12 : cluster 3 ω x₁ ≠ cluster 3 ω x₂) (h13 : cluster 3 ω x₁ ≠ cluster 3 ω x₃)
    (h23 : cluster 3 ω x₂ ≠ cluster 3 ω x₃) (h1 : lma_ClusterReachesRay ω x₁ j₁)
    (h2 : lma_ClusterReachesRay ω x₂ j₂) (h3 : lma_ClusterReachesRay ω x₃ j₃) :
    tex_AttachData ω x₁ x₂ x₃ :=
  lma_attachData_of_three_reachesRay ω x₁ x₂ x₃ j₁ j₂ j₃ h12 h13 h23 h1 h2 h3

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.LatticeMengerAttach
