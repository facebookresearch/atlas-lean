/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BernoulliErgodicFiniteEnergy
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmReachComponent
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestReaching
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SpanForestArms
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PeeledBoxForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxOpenForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafInjection
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalTrifCount

/-!
# Canonical counts from arm forests

Arm forest reaching and box open forests bound the canonical trifurcation count by the boundary
size.

## i. Overview

Canonical trifurcations have the arm data used by arm forest reaching. Arm forest reaching and the
box open forest bound `ctc2_canonTcount` by `|∂Λₙ|`. A single canonical trifurcation satisfies the
hypotheses.

## ii. Key results

- `ccf_canonTcount_le_boundary_of_armForestReaching` : the canonical count from arm forest reaching.

## iii. Table of contents

- A. Canonical counts

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Canonical counts -/

lemma ccf_canon_arm_data (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d),
      (∀ i, (openSubgraph d ω).Adj x (c i)) ∧
      (∀ i, c i ≠ x) ∧
      (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
       ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
       ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧
      (∀ i, zr i ∈ vertexBoundary d (n + 1) ∧
        ∃ w : (openSubgraph d (removeSite x ω)).Walk (c i) (zr i), x ∉ w.support) :=
  arc_trif_arm_data ω n (StatMech.Percolation.ctc2_armsRemoveSiteInfinite_of_canonical ω n hcanon)
      x hxbox htri

lemma ccf_canonTcount_le_boundary_of_armForestReaching (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : sfa_ArmForestReaching ω n) : ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n :=
  le_trans (ctc2_canonTcount_le_Tcount ω n)
      (StatMech.Percolation.sfa_Tcount_le_boundary_of_armForestReaching ω n h)

lemma ccf_canonTcount_le_boundary_of_boxOpenForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bst_BoxOpenForest ω n) : ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n :=
  le_trans (ctc2_canonTcount_le_Tcount ω n)
      (StatMech.Percolation.bst_Tcount_le_boundary_of_boxOpenForest ω n h)

lemma ccf_truthcheck_canon_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (hxbox : x ∈ box d n) (htri : IsCanonicalTrifurcation d ω x)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (c : Fin 3 → Site d)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (c i))
    (hne : ∀ i, c i ≠ x)
    (hcut : ¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
            ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
            ¬ Connected d (removeSite x ω) (c 1) (c 2))
    (hbdry : ∀ i, c i ∈ vertexBoundary d n)
    (hinj : Function.Injective c) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  StatMech.Percolation.arc_Tcount_le_boundary_of_residue_single_boundary ω n hxbox
      (ctc2_isTrifurcation_of_canonical htri) hsingle c hadj hne hcut
    hbdry hinj

end Percolation

end StatMech
