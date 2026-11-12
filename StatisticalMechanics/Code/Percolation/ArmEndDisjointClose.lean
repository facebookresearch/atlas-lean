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
import Code.Percolation.BurtonKeaneMerge
import Code.Percolation.TrifurcationCount
import Code.Percolation.BurtonKeaneClose2
import Code.Percolation.DisjointArmEndsClose
import Code.Percolation.DisjointArmEndsProve
import Code.Percolation.DisjointArmEndsProve2
import Code.Percolation.DisjointArmEndsFinal
import Code.Percolation.BKForestLib
import Code.Percolation.BKHallSDRClose

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}











theorem aed_globalCut_equiv (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    Equivalence (Connected d (removeSites T ω)) :=
  connected_equivalence (removeSites T ω)



def aed_sameGlobalComponent (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (u v : Site d) : Prop :=
  Connected d (removeSites T ω) u v





theorem aed_sameComponent_of_commonLeaf (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {u v w : Site d} (hu : Connected d (removeSites T ω) u w)
    (hv : Connected d (removeSites T ω) v w) :
    aed_sameGlobalComponent T ω u v :=
  hu.trans hv.symm















theorem aed_globalCutArmEnds_disjoint_of_distinct (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {u v : Site d}
    (hdis : ¬ aed_sameGlobalComponent T ω u v) :
    Disjoint (daep_globalCutArmEnds T ω n u) (daep_globalCutArmEnds T ω n v) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [daep_mem_globalCutArmEnds] at hw1 hw2
  exact hdis (aed_sameComponent_of_commonLeaf T ω hw1.2 hw2.2)
















theorem aed_hall_of_distinctComponents (T' : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (T : Finset (Site d)) (b : Site d → Site d)
    (hne : ∀ x ∈ T, (daep_globalCutArmEnds T' ω n (b x)).Nonempty)
    (hdistinct : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      ¬ aed_sameGlobalComponent T' ω (b x) (b y)) :
    ∀ S : Finset (Site d), S ⊆ T →
      S.card ≤ (S.biUnion (fun x => daep_globalCutArmEnds T' ω n (b x))).card :=
  bhs_hall_of_pairwiseDisjoint T (fun x => daep_globalCutArmEnds T' ω n (b x)) hne
    (fun x hx y hy hxy =>
      aed_globalCutArmEnds_disjoint_of_distinct T' ω n (hdistinct x hx y hy hxy))
























def aed_GlobalForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → ¬ aed_sameGlobalComponent (tfc_trifFinset ω n) ω (b x) (b y))













theorem aed_hallArmEnds_of_globalForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : aed_GlobalForestArms ω n) :
    bhs_HallArmEnds ω n := by
  classical
  obtain ⟨b, hexist, hdistinct⟩ := h
  set T := tfc_trifFinset ω n with hT
  refine ⟨b, hexist, ?_⟩
  
  refine aed_hall_of_distinctComponents T ω n T b ?_ ?_
  · 
    intro x hxT
    rw [hT, tfc_mem_trifFinset] at hxT
    obtain ⟨hbbox, _, hbinf⟩ := hexist x hxT.1 hxT.2
    exact daep_globalCutArmEnds_nonempty T ω n hn (b x) hbbox hbinf
  · 
    intro x hxT y hyT hxy
    rw [hT, tfc_mem_trifFinset] at hxT hyT
    exact hdistinct x hxT.1 hxT.2 y hyT.1 hyT.2 hxy













theorem aed_globalForestArms_of_globalCutSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daep_GlobalCutSeparation ω n) :
    aed_GlobalForestArms ω n := by
  obtain ⟨b, hexist, hsep⟩ := h
  exact ⟨b, hexist, fun x hxbox htri y hybox htriy hxy =>
    hsep x hxbox htri y hybox htriy hxy⟩



theorem aed_globalCutSeparation_of_globalForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : aed_GlobalForestArms ω n) :
    daep_GlobalCutSeparation ω n := by
  obtain ⟨b, hexist, hdistinct⟩ := h
  exact ⟨b, hexist, fun x hxbox htri y hybox htriy hxy =>
    hdistinct x hxbox htri y hybox htriy hxy⟩











theorem aed_globalForestArms_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    aed_GlobalForestArms ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _; exact absurd htri (hno x hxbox)






theorem aed_globalForestArms_of_disjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (b : Site d → Site d)
    (hexist : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hdistinct : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → x ≠ y →
      ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) (b x) (b y)) :
    aed_GlobalForestArms ω n :=
  ⟨b, hexist, hdistinct⟩






theorem aed_globalForestArms_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    aed_GlobalForestArms ω n :=
  aed_globalForestArms_of_globalCutSeparation ω n
    (daep_globalCutSeparation_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq)






theorem aed_Tcount_le_boundary_of_globalForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : aed_GlobalForestArms ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bhs_Tcount_le_boundary_of_hall ω n (aed_hallArmEnds_of_globalForestArms ω n hn h)















theorem aed_burton_keane_bernoulli_of_globalForestArms (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → aed_GlobalForestArms ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bhs_burton_keane_bernoulli_of_hall hd p hp1 hp0
    (fun ω n hn => aed_hallArmEnds_of_globalForestArms ω n hn (hres ω n hn))
    htrif














def aed_globalSetoid (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    Setoid (Site d) where
  r := Connected d (removeSites T ω)
  iseqv := aed_globalCut_equiv T ω




theorem aed_distinctComponent_iff_not_setoid (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (u v : Site d) :
    ¬ aed_sameGlobalComponent T ω u v ↔ ¬ (aed_globalSetoid T ω).r u v :=
  Iff.rfl






theorem aed_hall_of_disjointLeaves (T' : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (T : Finset (Site d)) (b : Site d → Site d)
    (hne : ∀ x ∈ T, (daep_globalCutArmEnds T' ω n (b x)).Nonempty)
    (hdisj : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      Disjoint (daep_globalCutArmEnds T' ω n (b x)) (daep_globalCutArmEnds T' ω n (b y))) :
    ∀ S : Finset (Site d), S ⊆ T →
      S.card ≤ (S.biUnion (fun x => daep_globalCutArmEnds T' ω n (b x))).card :=
  bhs_hall_of_pairwiseDisjoint T (fun x => daep_globalCutArmEnds T' ω n (b x)) hne hdisj







theorem aed_globalForestArms_of_forestPeel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bkfl_ForestPeel ω n) :
    aed_GlobalForestArms ω n :=
  aed_globalForestArms_of_globalCutSeparation ω n
    (daep2_globalCutSeparation_of_sameCluster ω n
      (daep2_sameClusterCutSeparation_of_singleCut ω n
        (daepf_singleCutBranchSeparation_of_privateArm ω n
          (bkfl_privateArm_of_forestPeel ω n h))))

end Percolation

end StatMech
