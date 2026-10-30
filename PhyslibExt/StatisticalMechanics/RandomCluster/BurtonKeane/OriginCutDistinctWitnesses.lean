/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalTrifCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoherentArmSelector
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeDisjointWitnesses
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CorridorCutUnbounded

/-!
# Infinite clusters after removing the origin

Of three distinct infinite clusters at most one contains the origin, so at least two stay infinite
when the origin is removed; the third does too if its punctured cluster has an infinite piece.

## i. Overview

A cluster that avoids the origin is unchanged by `removeSite 0`. Since distinct clusters are
disjoint, at most one of three distinct infinite clusters contains the origin, so at least two stay
infinite. `bc3_OriginCutLeavesInfinite ω` says that an infinite cluster containing the origin keeps
an infinite piece after the origin is removed; with it all three clusters provide infinite witnesses
(`bc3_DistinctWitnessClusters`).

## ii. Key results

- `bc3_twoArms_cutInfinite` : two of three distinct infinite clusters stay infinite
- `bc3_threeArms_cutInfinite_of_residue` : all three do under `bc3_OriginCutLeavesInfinite`
- `bc3_distinctWitnessClusters` : distinct witness clusters in every box

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}

/-! ## A. Results -/

lemma bc3_cutClusterEq_of_originNotMem (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h0 : (0 : Site d) ∉ cluster d ω x) :
    cluster d (removeSite 0 ω) x = cluster d ω x := by
  apply Set.Subset.antisymm
  · exact ctc2_cluster_removeSite_subset 0 x ω
  · intro y hy
    rw [mem_cluster] at hy ⊢
    obtain ⟨w⟩ := hy
    have havoid : (0 : Site d) ∉ w.support := fun hmem =>
      h0 (mem_cluster.mpr (w.takeUntil 0 hmem).reachable)
    exact pap_connected_removeSite_of_walk_avoid ω 0 w havoid

lemma bc3_cutClusterInfinite_of_originNotMem (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d ω x).Infinite) (h0 : (0 : Site d) ∉ cluster d ω x) :
    (cluster d (removeSite 0 ω) x).Infinite := by
  rw [bc3_cutClusterEq_of_originNotMem ω x h0]; exact hinf

lemma bc3_clusterEq_of_originMem (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hx : (0 : Site d) ∈ cluster d ω x) (hy : (0 : Site d) ∈ cluster d ω y) :
    cluster d ω x = cluster d ω y :=
  (cluster_eq_of_connected (mem_cluster.mp hx)).trans
    (cluster_eq_of_connected (mem_cluster.mp hy)).symm

lemma bc3_twoArms_avoid_origin (ω : ConfigSpace (Sym2 (Site d))) {x₁ x₂ x₃ : Site d}
    (hd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hd23 : cluster d ω x₂ ≠ cluster d ω x₃) :
    ((0 : Site d) ∉ cluster d ω x₁ ∧ (0 : Site d) ∉ cluster d ω x₂) ∨
      ((0 : Site d) ∉ cluster d ω x₁ ∧ (0 : Site d) ∉ cluster d ω x₃) ∨
      ((0 : Site d) ∉ cluster d ω x₂ ∧ (0 : Site d) ∉ cluster d ω x₃) := by
  by_cases h1 : (0 : Site d) ∈ cluster d ω x₁
  · exact Or.inr (Or.inr ⟨fun h2 => hd12 (bc3_clusterEq_of_originMem ω h1 h2),
      fun h3 => hd13 (bc3_clusterEq_of_originMem ω h1 h3)⟩)
  · by_cases h2 : (0 : Site d) ∈ cluster d ω x₂
    · exact Or.inr (Or.inl ⟨h1, fun h3 => hd23 (bc3_clusterEq_of_originMem ω h2 h3)⟩)
    · exact Or.inl ⟨h1, h2⟩

lemma bc3_twoArms_cutInfinite (ω : ConfigSpace (Sym2 (Site d))) {x₁ x₂ x₃ : Site d}
    (hi1 : (cluster d ω x₁).Infinite) (hi2 : (cluster d ω x₂).Infinite)
    (hi3 : (cluster d ω x₃).Infinite)
    (hd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hd23 : cluster d ω x₂ ≠ cluster d ω x₃) :
    ((cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite) ∨
      ((cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) ∨
      ((cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) := by
  rcases bc3_twoArms_avoid_origin ω hd12 hd13 hd23 with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨bc3_cutClusterInfinite_of_originNotMem ω x₁ hi1 a,
      bc3_cutClusterInfinite_of_originNotMem ω x₂ hi2 b⟩
  · exact Or.inr (Or.inl ⟨bc3_cutClusterInfinite_of_originNotMem ω x₁ hi1 a,
      bc3_cutClusterInfinite_of_originNotMem ω x₃ hi3 b⟩)
  · exact Or.inr (Or.inr ⟨bc3_cutClusterInfinite_of_originNotMem ω x₂ hi2 a,
      bc3_cutClusterInfinite_of_originNotMem ω x₃ hi3 b⟩)

/-- Every infinite cluster containing the origin keeps an infinite cluster after the origin is
removed. -/
def bc3_OriginCutLeavesInfinite (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∀ x : Site d, (cluster d ω x).Infinite → (0 : Site d) ∈ cluster d ω x →
    ∃ x', x' ∈ cluster d ω x ∧ (cluster d (removeSite 0 ω) x').Infinite

lemma bc3_arm_cutInfinite_of_residue (ω : ConfigSpace (Sym2 (Site d)))
    (hres : bc3_OriginCutLeavesInfinite ω) (x : Site d) (hinf : (cluster d ω x).Infinite) :
    ∃ x', x' ∈ cluster d ω x ∧ (cluster d (removeSite 0 ω) x').Infinite := by
  by_cases h0 : (0 : Site d) ∈ cluster d ω x
  · exact hres x hinf h0
  · exact ⟨x, self_mem_cluster ω x, bc3_cutClusterInfinite_of_originNotMem ω x hinf h0⟩

lemma bc3_armEscapes_of_cutInfinite (ω : ConfigSpace (Sym2 (Site d))) (x' : Site d)
    (hinf : (cluster d (removeSite 0 ω) x').Infinite) (n : ℕ) :
    ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x' y ∧
      (cluster d (removeSite 0 ω) y).Infinite ∧ y ≠ 0 :=
  bc2_cutUnbounded ω x' hinf n

/-- In every configuration with three distinct infinite clusters meeting `B_n` there are three such
clusters with witnesses whose clusters stay infinite after the origin is removed. -/
def bc3_DistinctWitnessClusters (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∃ x₁ x₂ x₃ : Site d, x₁ ∈ box d n ∧ x₂ ∈ box d n ∧ x₃ ∈ box d n ∧
      (cluster d ω x₁).Infinite ∧ (cluster d ω x₂).Infinite ∧ (cluster d ω x₃).Infinite ∧
      cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃ ∧
      ∃ x₁' x₂' x₃' : Site d, x₁' ∈ cluster d ω x₁ ∧ x₂' ∈ cluster d ω x₂ ∧
        x₃' ∈ cluster d ω x₃ ∧
        (cluster d (removeSite 0 ω) x₁').Infinite ∧
        (cluster d (removeSite 0 ω) x₂').Infinite ∧
        (cluster d (removeSite 0 ω) x₃').Infinite

lemma bc3_threeArms_cutInfinite_of_residue (ω : ConfigSpace (Sym2 (Site d)))
    (hres : bc3_OriginCutLeavesInfinite ω) {x₁ x₂ x₃ : Site d}
    (hi1 : (cluster d ω x₁).Infinite) (hi2 : (cluster d ω x₂).Infinite)
    (hi3 : (cluster d ω x₃).Infinite) :
    ∃ x₁' x₂' x₃' : Site d, x₁' ∈ cluster d ω x₁ ∧ x₂' ∈ cluster d ω x₂ ∧
      x₃' ∈ cluster d ω x₃ ∧
      (cluster d (removeSite 0 ω) x₁').Infinite ∧
      (cluster d (removeSite 0 ω) x₂').Infinite ∧
      (cluster d (removeSite 0 ω) x₃').Infinite := by
  obtain ⟨x₁', hx₁', hinf₁⟩ := bc3_arm_cutInfinite_of_residue ω hres x₁ hi1
  obtain ⟨x₂', hx₂', hinf₂⟩ := bc3_arm_cutInfinite_of_residue ω hres x₂ hi2
  obtain ⟨x₃', hx₃', hinf₃⟩ := bc3_arm_cutInfinite_of_residue ω hres x₃ hi3
  exact ⟨x₁', x₂', x₃', hx₁', hx₂', hx₃', hinf₁, hinf₂, hinf₃⟩

lemma bc3_distinctWitnessClusters (n : ℕ)
    (hres : ∀ ω ∈ threeMeetBox d n, bc3_OriginCutLeavesInfinite ω) :
    bc3_DistinctWitnessClusters d n := by
  intro ω hω
  obtain ⟨x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23⟩ :=
    bc2_threeWitnesses n ω hω
  obtain ⟨x₁', x₂', x₃', hx₁', hx₂', hx₃', hinf₁, hinf₂, hinf₃⟩ :=
    bc3_threeArms_cutInfinite_of_residue ω (hres ω hω) hi1 hi2 hi3
  exact ⟨x₁, x₂, x₃, hb1, hb2, hb3, hi1, hi2, hi3, hd12, hd13, hd23,
    x₁', x₂', x₃', hx₁', hx₂', hx₃', hinf₁, hinf₂, hinf₃⟩

lemma bc3_distinctWitnessClusters_nonvacuous (ω : ConfigSpace (Sym2 (Site d)))
    {x₁ x₂ x₃ : Site d}
    (hi1 : (cluster d ω x₁).Infinite) (hi2 : (cluster d ω x₂).Infinite)
    (hi3 : (cluster d ω x₃).Infinite)
    (h01 : (0 : Site d) ∉ cluster d ω x₁) (h02 : (0 : Site d) ∉ cluster d ω x₂)
    (h03 : (0 : Site d) ∉ cluster d ω x₃) :
    (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧
      (cluster d (removeSite 0 ω) x₃).Infinite :=
  ⟨bc3_cutClusterInfinite_of_originNotMem ω x₁ hi1 h01,
    bc3_cutClusterInfinite_of_originNotMem ω x₂ hi2 h02,
    bc3_cutClusterInfinite_of_originNotMem ω x₃ hi3 h03⟩

lemma bc3_originCutLeavesInfinite_of_origin_isolated (ω : ConfigSpace (Sym2 (Site d)))
    (hnone : ∀ x, (cluster d ω x).Infinite → (0 : Site d) ∉ cluster d ω x) :
    bc3_OriginCutLeavesInfinite ω := by
  intro x hinf h0
  exact absurd h0 (hnone x hinf)

lemma bc3_distinctWitnessClusters_node (n : ℕ) :
    ((∀ ω ∈ threeMeetBox d n, bc3_OriginCutLeavesInfinite ω) →
        bc3_DistinctWitnessClusters d n) ∧
      (∀ (ω : ConfigSpace (Sym2 (Site d))) {x₁ x₂ x₃ : Site d},
        (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
        cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
        cluster d ω x₂ ≠ cluster d ω x₃ →
        ((cluster d (removeSite 0 ω) x₁).Infinite ∧
            (cluster d (removeSite 0 ω) x₂).Infinite) ∨
          ((cluster d (removeSite 0 ω) x₁).Infinite ∧
            (cluster d (removeSite 0 ω) x₃).Infinite) ∨
          ((cluster d (removeSite 0 ω) x₂).Infinite ∧
            (cluster d (removeSite 0 ω) x₃).Infinite)) :=
  ⟨fun hres => bc3_distinctWitnessClusters n hres,
    fun ω {_ _ _} hi1 hi2 hi3 hd12 hd13 hd23 =>
      bc3_twoArms_cutInfinite ω hi1 hi2 hi3 hd12 hd13 hd23⟩

end Walls

end StatMech
