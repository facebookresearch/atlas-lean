/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.TrifurcationCount
import Code.Percolation.BurtonKeaneClose
import Code.Percolation.ArmReachComponentClose
import Code.Percolation.SpanForestArmsClose
import Code.Percolation.SecondPeelingClose
import Code.Percolation.OpenSpanningForestClose
import Code.Percolation.BKSpanningTreeClose
import Code.Percolation.ForestLeafInjection
import Code.Percolation.CanonicalTrifCount

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}














theorem ccf_armsRemoveSiteInfinite_of_canonical (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x) :
    arc_TrifArmsRemoveSiteInfinite ω n :=
  ctc2_armsRemoveSiteInfinite_of_canonical ω n hcanon






theorem ccf_canon_arm_data (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
  arc_trif_arm_data ω n (ccf_armsRemoveSiteInfinite_of_canonical ω n hcanon) x hxbox htri












theorem ccf_canon_count_of_armForestReaching (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : sfa_ArmForestReaching ω n) : Tcount d ω n ≤ boxSV_boundaryCard d n :=
  sfa_Tcount_le_boundary_of_armForestReaching ω n h



theorem ccf_canon_count_of_boxOpenForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bst_BoxOpenForest ω n) : Tcount d ω n ≤ boxSV_boundaryCard d n :=
  fli_Tcount_le_boundary_of_boxOpenForest ω n h












theorem ccf_canon_count_single (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x)
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
  arc_Tcount_le_boundary_of_residue_single_boundary ω n hxbox htri hsingle c hadj hne hcut
    hbdry hinj






theorem ccf_canon_count_subsingleton (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n →
      IsTrifurcation d ω y → x = y) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  ctc2_count_of_subsingleton ω n hn hsub












theorem ccf_canonTcount_le_boundary_of_armForestReaching (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : sfa_ArmForestReaching ω n) : ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n :=
  le_trans (ctc2_canonTcount_le_Tcount ω n) (ccf_canon_count_of_armForestReaching ω n h)



theorem ccf_canonTcount_le_boundary_of_boxOpenForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bst_BoxOpenForest ω n) : ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n :=
  le_trans (ctc2_canonTcount_le_Tcount ω n) (ccf_canon_count_of_boxOpenForest ω n h)




theorem ccf_canonTcount_le_boundary_subsingleton (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n)
    (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n →
      IsTrifurcation d ω y → x = y) :
    ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n :=
  ctc2_canonTcount_le_boundary_of_subsingleton ω n hn hsub














theorem ccf_truthcheck_canon_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
  ccf_canon_count_single ω n hxbox (ctc2_isTrifurcation_of_canonical htri) hsingle c hadj hne hcut
    hbdry hinj

end Percolation

end StatMech
