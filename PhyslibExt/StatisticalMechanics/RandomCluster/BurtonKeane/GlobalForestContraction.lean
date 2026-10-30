/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ContractedGraphDegree
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SublatticeForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HarmBoxCoarseReach

/-!
# Global forests from contracted trifurcation graphs

A contracted trifurcation graph gives the global contracted forest, and with it the coarse
trifurcation count.

## i. Overview

`bc103_ContractedTrifGraph` provides a graph on the contracted lattice in which every coarse
trifurcation separates three neighbours. Its spanning forest keeps degree three at such vertices,
which gives `bc69_Gn_globalForest` and the coarse counting bound. The forest exists trivially when
there is no coarse trifurcation.

The trifurcation notion here is the coarse one on `L`-boxes (`bc61_IsCoarseTrifurcation`,
`bc67_IsGnTrifurcation`), whose arms are infinite after the whole `L`-box is removed. Results that
assume a certificate for every configuration are conditional: no such certificate is constructed for
all configurations.

## ii. Key results

- `bc110_globalForest_of_contracted` : a contracted trifurcation graph gives the global forest
- `bc110_status` : the statements together

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

lemma bc110_globalForest_of_contracted (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc103_ContractedTrifGraph ω L R) : bc69_Gn_globalForest ω L R :=
  bc103_globalForest_of_contractedGraph ω L R h

lemma bc110_globalForest_all_free_except_contraction (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc103_ContractedTrifGraph ω L R) :
    bc69_Gn_globalForest ω L R ∧
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V), (osf_spanForest G).IsAcyclic) ∧
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel (osf_spanForest G).Adj]
      {u v₁ v₂ v₃ : V}, G.Adj u v₁ → G.Adj u v₂ → G.Adj u v₃ →
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂ →
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃ →
      ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃ →
      3 ≤ (osf_spanForest G).degree u) := by
  refine ⟨bc110_globalForest_of_contracted ω L R h, ?_, ?_⟩
  · intro V _ G; exact osf_spanForest_acyclic G
  · intro V _ G _ u v₁ v₂ v₃ h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃
    exact bc103_deg3_spanForest_of_noBypass G h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃

lemma bc110_contractionArm_of_trif (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y : Site d}
    (h : bc67_IsGnTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
      ((cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧
       (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧
       (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite) ∧
      (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) :=
  h

lemma bc110_globalForest_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc69_Gn_globalForest ω L R :=
  bc69_globalForest_of_noTrif ω L R hz₀ hz₁ hzne hno


/-! ## B. Summary -/

open Classical in
lemma bc110_status :
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc103_ContractedTrifGraph ω L R → bc69_Gn_globalForest ω L R) ∧
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel (osf_spanForest G).Adj]
      (u v₁ v₂ v₃ : V), G.Adj u v₁ → G.Adj u v₂ → G.Adj u v₃ →
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂ →
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃ →
      ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃ →
      3 ≤ (osf_spanForest G).degree u) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d),
      bc67_IsGnTrifurcation ω L y →
      ∃ a₁ a₂ a₃ : Site d,
        (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
         ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
         ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃)) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L R h; exact bc110_globalForest_of_contracted ω L R h
  · intro V _ G _ u v₁ v₂ v₃ h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃
    exact bc103_deg3_spanForest_of_noBypass G h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃
  · intro ω L y h
    obtain ⟨a₁, a₂, a₃, _, _, hcut⟩ := h
    exact ⟨a₁, a₂, a₃, hcut⟩
  · intro ω L R h; exact bc69_count_via_leafBound ω L R h

end StatMech.Walls
