/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Walls.bc8core
import Code.Walls.bc8distinctcutclusters
import Code.Walls.bc8nocrossing

open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}




























def bc9_DistinctCutClusters (d n : ℕ) : Prop :=
  (∀ ω ∈ threeMeetBox d n,
      ∃ x₁ x₂ x₃ : Site d,
        (cluster d (removeSite 0 ω) x₁).Infinite ∧
        (cluster d (removeSite 0 ω) x₂).Infinite ∧
        (cluster d (removeSite 0 ω) x₃).Infinite ∧
        cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧
        cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧
        cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d),
      cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y →
        ∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x →
          ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) y →
            ¬ IsOpenEdge d (removeSite 0 ω) u v)












theorem bc9_distinctCutClusters (n : ℕ) : bc9_DistinctCutClusters d n :=
  ⟨fun ω hω => bc8_threeArmClusters_distinct n ω hω,
   fun _ω _x _y hne => bc8_cut_no_crossing hne⟩










theorem bc9_threeArms_distinct (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hω : ω ∈ threeMeetBox d n) :
    ∃ x₁ x₂ x₃ : Site d,
      (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧
      (cluster d (removeSite 0 ω) x₃).Infinite ∧
      cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧
      cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧
      cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃ :=
  (bc9_distinctCutClusters n).1 ω hω








theorem bc9_cut_no_crossing (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hne : cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y) :
    ∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x →
      ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) y →
        ¬ IsOpenEdge d (removeSite 0 ω) u v :=
  (bc9_distinctCutClusters (n := 0)).2 ω x y hne




















theorem bc9_threeArms_pairwiseNoMerge (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hω : ω ∈ threeMeetBox d n) :
    ∃ x₁ x₂ x₃ : Site d,
      (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧
      (cluster d (removeSite 0 ω) x₃).Infinite ∧
      cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧
      cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧
      cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃ ∧
      Disjoint (cluster d (removeSite 0 ω) x₁) (cluster d (removeSite 0 ω) x₂) ∧
      Disjoint (cluster d (removeSite 0 ω) x₁) (cluster d (removeSite 0 ω) x₃) ∧
      Disjoint (cluster d (removeSite 0 ω) x₂) (cluster d (removeSite 0 ω) x₃) ∧
      (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₁ →
        ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₂ →
          ¬ IsOpenEdge d (removeSite 0 ω) u v) ∧
      (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₁ →
        ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₃ →
          ¬ IsOpenEdge d (removeSite 0 ω) u v) ∧
      (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₂ →
        ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₃ →
          ¬ IsOpenEdge d (removeSite 0 ω) u v) := by
  obtain ⟨x₁, x₂, x₃, hi1, hi2, hi3, hd12, hd13, hd23⟩ := bc9_threeArms_distinct n ω hω
  exact ⟨x₁, x₂, x₃, hi1, hi2, hi3, hd12, hd13, hd23,
    bc8_disjoint_of_cut_ne hd12, bc8_disjoint_of_cut_ne hd13, bc8_disjoint_of_cut_ne hd23,
    bc9_cut_no_crossing ω hd12, bc9_cut_no_crossing ω hd13, bc9_cut_no_crossing ω hd23⟩













theorem bc9_noCrossing_of_node (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    bc8_NoCrossing ω x y :=
  bc8_noCrossing ω x y





















theorem bc9_distinctCutClusters_originRewiring (n : ℕ) (hrw : bc8_OriginRewiring d n)
    (ω : ConfigSpace (Sym2 (Site d))) (hω : ω ∈ threeMeetBox d n) :
    ∃ W : Finset (Sym2 (Site d)), (∀ e ∈ W, (0 : Site d) ∉ e) ∧
      IsCanonicalTrifurcation d (forceOpenFinset W ω) 0 :=
  bc8_canonicalTrif_of_originRewiring n hrw ω hω



section AxiomAudit


#guard_msgs in
#print axioms bc9_distinctCutClusters


#guard_msgs in
#print axioms bc9_threeArms_distinct


#guard_msgs in
#print axioms bc9_cut_no_crossing


#guard_msgs in
#print axioms bc9_threeArms_pairwiseNoMerge


#guard_msgs in
#print axioms bc9_distinctCutClusters_originRewiring

end AxiomAudit

end Walls

end StatMech
