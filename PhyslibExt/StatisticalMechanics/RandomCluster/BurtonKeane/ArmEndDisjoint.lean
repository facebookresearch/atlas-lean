/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneMerge
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndsDistinct
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafInjectionBound
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateArmTwoTrif
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HallArmEnds

/-!
# Global forest arms and disjoint arm ends

Global cut components give disjoint arm-end sets and Hall's condition; global forest arms are
equivalent to global cut separation and give the trifurcation count.

## i. Overview

Connectivity after removing a finite set `T` is an equivalence relation (`aed_globalSetoid`).
Arm-end sets of sites in different components are disjoint, so distinct components give Hall's
condition for a system of distinct boundary representatives. `aed_GlobalForestArms ω n` asks for arm
ends lying in distinct global components. It is equivalent to `daep_GlobalCutSeparation`, gives Hall
arm ends and the count bound, and holds with no trifurcation, one trifurcation or a forest peel.

**Fidelity.** `aed_burton_keane_bernoulli_of_globalForestArms` assumes global forest arms for every
configuration and box, which implies the configuration-wide trifurcation bound refuted by
`tfc_not_forall_Tcount_le_boundary`; it is vacuous and kept only because another lane uses it.

## ii. Key results

- `aed_globalCutArmEnds_disjoint_of_distinct` : arm-end sets of distinct components are disjoint.
- `aed_globalCutSeparation_of_globalForestArms` : global forest arms give global cut separation.
- `aed_Tcount_le_boundary_of_globalForestArms` : the count bound.

## iii. Table of contents

- A. Global cut components
- B. Global forest arms
- C. The setoid of components

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

/-! ## A. Global cut components -/

lemma aed_globalCut_equiv (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    Equivalence (Connected d (removeSites T ω)) :=
  connected_equivalence (removeSites T ω)

/-- `u` and `v` are connected after removing the finite set `T`. -/
def aed_sameGlobalComponent (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (u v : Site d) : Prop :=
  Connected d (removeSites T ω) u v

lemma aed_sameComponent_of_commonLeaf (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {u v w : Site d} (hu : Connected d (removeSites T ω) u w)
    (hv : Connected d (removeSites T ω) v w) :
    aed_sameGlobalComponent T ω u v :=
  hu.trans hv.symm

lemma aed_globalCutArmEnds_disjoint_of_distinct (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {u v : Site d}
    (hdis : ¬ aed_sameGlobalComponent T ω u v) :
    Disjoint (daep_globalCutArmEnds T ω n u) (daep_globalCutArmEnds T ω n v) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [daep_mem_globalCutArmEnds] at hw1 hw2
  exact hdis (aed_sameComponent_of_commonLeaf T ω hw1.2 hw2.2)

lemma aed_hall_of_distinctComponents (T' : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (T : Finset (Site d)) (b : Site d → Site d)
    (hne : ∀ x ∈ T, (daep_globalCutArmEnds T' ω n (b x)).Nonempty)
    (hdistinct : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      ¬ aed_sameGlobalComponent T' ω (b x) (b y)) :
    ∀ S : Finset (Site d), S ⊆ T →
      S.card ≤ (S.biUnion (fun x => daep_globalCutArmEnds T' ω n (b x))).card :=
  bhs_hall_of_pairwiseDisjoint T (fun x => daep_globalCutArmEnds T' ω n (b x)) hne
    (fun x hx y hy hxy =>
      aed_globalCutArmEnds_disjoint_of_distinct T' ω n (hdistinct x hx y hy hxy))

/-! ## B. Global forest arms -/

/-- Global forest arms for the box of radius `n`: arm ends `b x` with infinite clusters after
removing
`x`, lying in pairwise distinct components after removing all trifurcations of the box. -/
def aed_GlobalForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → ¬ aed_sameGlobalComponent (tfc_trifFinset ω n) ω (b x) (b y))

lemma aed_hallArmEnds_of_globalForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : aed_GlobalForestArms ω n) :
    bhs_HallArmEnds ω n := by
  classical
  obtain ⟨b, hexist, hdistinct⟩ := h
  set T := tfc_trifFinset ω n with hT
  refine ⟨b, hexist, ?_⟩
  refine aed_hall_of_distinctComponents T ω n T b ?_ ?_
  · intro x hxT
    rw [hT, tfc_mem_trifFinset] at hxT
    obtain ⟨hbbox, _, hbinf⟩ := hexist x hxT.1 hxT.2
    exact daep_globalCutArmEnds_nonempty T ω n hn (b x) hbbox hbinf
  · intro x hxT y hyT hxy
    rw [hT, tfc_mem_trifFinset] at hxT hyT
    exact hdistinct x hxT.1 hxT.2 y hyT.1 hyT.2 hxy

lemma aed_globalForestArms_of_globalCutSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daep_GlobalCutSeparation ω n) :
    aed_GlobalForestArms ω n := by
  obtain ⟨b, hexist, hsep⟩ := h
  exact ⟨b, hexist, fun x hxbox htri y hybox htriy hxy =>
    hsep x hxbox htri y hybox htriy hxy⟩

lemma aed_globalCutSeparation_of_globalForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : aed_GlobalForestArms ω n) :
    daep_GlobalCutSeparation ω n := by
  obtain ⟨b, hexist, hdistinct⟩ := h
  exact ⟨b, hexist, fun x hxbox htri y hybox htriy hxy =>
    hdistinct x hxbox htri y hybox htriy hxy⟩

lemma aed_globalForestArms_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    aed_GlobalForestArms ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _; exact absurd htri (hno x hxbox)

lemma aed_globalForestArms_of_disjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (b : Site d → Site d)
    (hexist : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hdistinct : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → x ≠ y →
      ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) (b x) (b y)) :
    aed_GlobalForestArms ω n :=
  ⟨b, hexist, hdistinct⟩

lemma aed_globalForestArms_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    aed_GlobalForestArms ω n :=
  aed_globalForestArms_of_globalCutSeparation ω n
    (daep_globalCutSeparation_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq)

lemma aed_Tcount_le_boundary_of_globalForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : aed_GlobalForestArms ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bhs_Tcount_le_boundary_of_hall ω n (aed_hallArmEnds_of_globalForestArms ω n hn h)

/-- Burton–Keane uniqueness from global forest arms for every configuration and box. Its
configuration-wide hypothesis implies `Tcount d ω n ≤ boxSV_boundaryCard d n` for every
configuration and box, which is false for `d ≥ 1` (`tfc_not_forall_Tcount_le_boundary`), so the
statement is vacuous. -/
lemma aed_burton_keane_bernoulli_of_globalForestArms (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
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

/-! ## C. The setoid of components -/

/-- The setoid of connectivity after removing `T`. -/
def aed_globalSetoid (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    Setoid (Site d) where
  r := Connected d (removeSites T ω)
  iseqv := aed_globalCut_equiv T ω

lemma aed_distinctComponent_iff_not_setoid (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (u v : Site d) :
    ¬ aed_sameGlobalComponent T ω u v ↔ ¬ (aed_globalSetoid T ω).r u v :=
  Iff.rfl

lemma aed_hall_of_disjointLeaves (T' : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (T : Finset (Site d)) (b : Site d → Site d)
    (hne : ∀ x ∈ T, (daep_globalCutArmEnds T' ω n (b x)).Nonempty)
    (hdisj : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      Disjoint (daep_globalCutArmEnds T' ω n (b x)) (daep_globalCutArmEnds T' ω n (b y))) :
    ∀ S : Finset (Site d), S ⊆ T →
      S.card ≤ (S.biUnion (fun x => daep_globalCutArmEnds T' ω n (b x))).card :=
  bhs_hall_of_pairwiseDisjoint T (fun x => daep_globalCutArmEnds T' ω n (b x)) hne hdisj

lemma aed_globalForestArms_of_forestPeel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bkfl_ForestPeel ω n) :
    aed_GlobalForestArms ω n :=
  aed_globalForestArms_of_globalCutSeparation ω n
    (daep2_globalCutSeparation_of_sameCluster ω n
      (daep2_sameClusterCutSeparation_of_singleCut ω n
        (daepf_singleCutBranchSeparation_of_privateArm ω n
          (bkfl_privateArm_of_forestPeel ω n h))))

end Percolation

end StatMech
