/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginAvoidingResidues

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginAvoidingResidues`

* `arr_three_residues_of_reachOrigin` as a conditional statement in `ℤ²` and `ℤ³`: three clusters
  reaching the origin give three origin-avoiding routing residues.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginAvoidingResidues

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

-- Three residues in `ℤ²`.
example (ω : ConfigSpace (Sym2 (Site 2))) (h : mco_ThreeClustersReachOrigin ω) :
    ∃ x₁ x₂ x₃ : Site 2, ava_AvoidingRoutingResidue ω x₁ ∧
      ava_AvoidingRoutingResidue ω x₂ ∧ ava_AvoidingRoutingResidue ω x₃ :=
  arr_three_residues_of_reachOrigin ω h

-- Three residues in `ℤ³`, with the first one named.
example (ω : ConfigSpace (Sym2 (Site 3))) (h : mco_ThreeClustersReachOrigin ω) :
    ∃ x : Site 3, ava_AvoidingRoutingResidue ω x := by
  obtain ⟨x₁, -, -, h₁, -, -⟩ := arr_three_residues_of_reachOrigin ω h
  exact ⟨x₁, h₁⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginAvoidingResidues
