/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Filter.Defs
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedTrifContraction
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmLeafBoundary
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ContractedGraphDegree

/-!
# Global forests give sublattice fibre bounds

The global contracted forest gives the fibre bound for every residue; leaves of distinct hubs can
share boundary sites, so a boundary injection from all arms fails.

## i. Overview

Each residue fibre is contained in the coarse trifurcation set, so a global forest bounds every
fibre. At each hub three forest neighbours are distinct. Arms of distinct hubs can reach the same
boundary site, which refutes a boundary injection from all arms; the forest leaf count is the
correct bound.

The trifurcation notion here is the coarse one on `L`-boxes (`bc61_IsCoarseTrifurcation`,
`bc67_IsGnTrifurcation`), whose arms are infinite after the whole `L`-box is removed. Results that
assume a certificate for every configuration are conditional: no such certificate is constructed for
all configurations.

## ii. Key results

- `bc108_sublatticeForest_of_contractedGraph` : a contracted graph gives the fibre bound
- `bc108_status` : the statements together

## iii. Table of contents

- A. Results
- B. Summary

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Results -/

lemma bc108_sublatticeForest_of_contractedGraph (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc103_ContractedTrifGraph ω L R) : bc73_SublatticeForest ω L R :=
  bc74_sublatticeForest_of_globalForest ω L R (bc103_globalForest_of_contractedGraph ω L R h)

lemma bc108_separatedCount_le_of_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) :
    bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc106_separated_count_le_boundary_of_forest ω L R (bc74_sublatticeForest_of_globalForest ω L R h)

lemma bc108_full_covering_of_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) :
    bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R :=
  bc73_covering ω L R (bc74_sublatticeForest_of_globalForest ω L R h)

lemma bc108_bk_count_reduces_to_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    (bc69_Gn_globalForest ω L R → bc73_SublatticeForest ω L R) ∧
    (bc69_Gn_globalForest ω L R → bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    (bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) :=
  ⟨bc74_sublatticeForest_of_globalForest ω L R,
   bc108_separatedCount_le_of_globalForest ω L R,
   bc69_coarseTcount_le_boundary ω L R⟩

lemma bc108_sublatticeForest_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc73_SublatticeForest ω L R :=
  bc74_sublatticeForest_of_globalForest ω L R
    (bc69_globalForest_of_noTrif ω L R hz₀ hz₁ hzne hno)

/-! ## B. Summary -/

lemma bc108_status :
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc73_SublatticeForest ω L R) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)),
      (bc73_fiber ω L R c).card ≤ bc61_coarseTcount ω L R) ∧
    (∀ (L : ℕ),
      Disjoint (bc61_boxAround 2 L (0 : Site 2))
          (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
        Connected 2 bc60_upperLines
          (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) ∧
    (∀ {V : Type} {G : SimpleGraph V} (u v₁ v₂ v₃ : V),
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂ →
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃ →
      ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃ →
      v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω L R h; exact bc74_sublatticeForest_of_globalForest ω L R h
  · intro ω L R c; exact bc74_fiber_card_le_coarseTcount ω L R c
  · intro L; exact bc64_arms_can_share_boundary L
  · intro V G u v₁ v₂ v₃ hc₁₂ hc₁₃ hc₂₃; exact bc103_arms_distinct_of_deleteVert_cut hc₁₂ hc₁₃ hc₂₃
  · intro ω L R h; exact bc108_separatedCount_le_of_globalForest ω L R h

end StatMech.Walls

