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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndsDistinct

/-!
# Leaf injections and distinct arm ends

An injection from trifurcations to connected boundary sites is the same as a choice of distinct arm
ends, and it bounds the trifurcation count by the boundary size.

## i. Overview

`daec_ForestLeafInjection ω n` asks for a map sending each trifurcation of the box to a boundary
site it is connected to, injectively on trifurcations. It is equivalent to `tfc_DistinctArmEnds` and
gives `Tcount ≤ |∂B_n|`. The file also shows that pairwise disjoint arm ends cannot hold for two
connected trifurcations, and it records the degenerate cases (at most one trifurcation) where the
certificate is immediate.

No certificate of this kind can hold for every configuration: each one yields the
trifurcation-to-boundary injection `tfc_DistinctArmEnds`, and `tfc_not_forall_distinctArmEnds` shows
that this injection fails for some configuration in every dimension `d ≥ 1` (in `tfc_lineConfig`
every site is a trifurcation in the sense of `IsTrifurcation`). The certificate is useful
configuration by configuration; the deterministic counting bound is the reusable content.

## ii. Key results

- `daec_forestLeafInjection_iff_distinctArmEnds` : the certificate is `tfc_DistinctArmEnds`
- `daec_Tcount_le_boundary_of_forestLeafInjection` : the counting bound
- `daec_disjointArmEnds_false_of_connected_trif` : two connected trifurcations never have disjoint
  arm ends
- `daec_forestLeafInjection_of_subsingleton` : the certificate when there is at most one
  trifurcation

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Results -/

lemma daec_armEnds_eq_of_connected (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {x y : Site d}
    (hxy : Connected d ω x y) :
    bk2_armEndFinset ω n x = bk2_armEndFinset ω n y := by
  classical
  apply Finset.ext
  intro z
  rw [bk2_mem_armEndFinset, bk2_mem_armEndFinset]
  refine ⟨fun h => ⟨h.1, hxy.symm.trans h.2⟩, fun h => ⟨h.1, hxy.trans h.2⟩⟩

lemma daec_not_disjoint_of_connected_trif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) {x y : Site d} (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x)
    (_hybox : y ∈ box d n) (_htriy : IsTrifurcation d ω y) (hconn : Connected d ω x y) :
    ¬ Disjoint (bk2_armEndFinset ω n x) (bk2_armEndFinset ω n y) := by
  have heq := daec_armEnds_eq_of_connected ω n (d := d) hconn
  rw [heq, disjoint_self, Finset.bot_eq_empty]
  exact (heq ▸ bk2_armEndFinset_nonempty ω n hn x hxbox htri).ne_empty

lemma daec_disjointArmEnds_false_of_connected_trif (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) {x y : Site d}
    (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x)
    (hybox : y ∈ box d n) (htriy : IsTrifurcation d ω y)
    (hxy : x ≠ y) (hconn : Connected d ω x y) :
    ¬ bk2_DisjointArmEnds ω n := by
  intro hdisj
  exact daec_not_disjoint_of_connected_trif ω n hn hxbox htri hybox htriy hconn
    (hdisj x hxbox htri y hybox htriy hxy)

lemma daec_disjointArmEnds_forces_separation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hdisj : bk2_DisjointArmEnds ω n) :
    ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → ¬ Connected d ω x y := by
  intro x hxbox htri y hybox htriy hxy hconn
  exact daec_disjointArmEnds_false_of_connected_trif ω n hn hxbox htri hybox htriy hxy hconn
    hdisj

lemma daec_disjointArmEnds_refutable_on_spanned (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) {x y : Site d}
    (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x)
    (hybox : y ∈ box d n) (htriy : IsTrifurcation d ω y) (hxy : x ≠ y)
    (hspan : ∀ u v, u ∈ box d n → IsTrifurcation d ω u → v ∈ box d n →
      IsTrifurcation d ω v → Connected d ω u v) :
    ¬ bk2_DisjointArmEnds ω n :=
  daec_disjointArmEnds_false_of_connected_trif ω n hn hxbox htri hybox htriy hxy
    (hspan x y hxbox htri hybox htriy)

lemma daec_trif_removeSite_three_distinct (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) {x a₁ a₂ a₃ : Site d}
    (hx : Connected d ω x a₁) (hx2 : Connected d ω x a₂) (hx3 : Connected d ω x a₃)
    (ha1box : a₁ ∈ box d n) (ha2box : a₂ ∈ box d n) (ha3box : a₃ ∈ box d n)
    (hi1 : (cluster d (removeSite x ω) a₁).Infinite)
    (hi2 : (cluster d (removeSite x ω) a₂).Infinite)
    (hi3 : (cluster d (removeSite x ω) a₃).Infinite)
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
    ∃ z₁ z₂ z₃ : Site d,
      (z₁ ∈ vertexBoundary d n ∧ z₂ ∈ vertexBoundary d n ∧ z₃ ∈ vertexBoundary d n) ∧
      (Connected d ω x z₁ ∧ Connected d ω x z₂ ∧ Connected d ω x z₃) ∧
      (¬ Connected d (removeSite x ω) z₁ z₂ ∧ ¬ Connected d (removeSite x ω) z₁ z₃ ∧
        ¬ Connected d (removeSite x ω) z₂ z₃) ∧
      (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
  obtain ⟨z₁, z₂, z₃, hzb, hzc, hzd, hzne⟩ :=
    bk2_trif_three_disjoint_boundary ω n hn ha1box ha2box ha3box hi1 hi2 hi3 hd12 hd13 hd23
  have hle : removeSite x ω ≤ ω := by
    intro e; unfold removeSite; by_cases h : x ∈ e <;> simp [h]
  refine ⟨z₁, z₂, z₃, hzb, ⟨?_, ?_, ?_⟩, hzd, hzne⟩
  · exact hx.trans (connected_mono hle hzc.1)
  · exact hx2.trans (connected_mono hle hzc.2.1)
  · exact hx3.trans (connected_mono hle hzc.2.2)

/-- A forest-leaf injection for the box `B_n`: every trifurcation in `B_n` is sent to a boundary
site it is connected to, and distinct trifurcations go to distinct sites. -/
def daec_ForestLeafInjection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ φ : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      φ x ∈ vertexBoundary d n ∧ Connected d ω x (φ x)) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → φ x = φ y → x = y)

lemma daec_forestLeafInjection_iff_distinctArmEnds (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) : daec_ForestLeafInjection ω n ↔ tfc_DistinctArmEnds ω n := Iff.rfl

lemma daec_distinctArmEnds_of_forestLeafInjection (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : daec_ForestLeafInjection ω n) : tfc_DistinctArmEnds ω n := h

lemma daec_forestLeafInjection_of_subsingleton (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n)
    (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n →
      IsTrifurcation d ω y → x = y) :
    daec_ForestLeafInjection ω n :=
  tfc_distinctArmEnds_of_subsingleton ω n hn hsub

lemma daec_Tcount_le_boundary_of_forestLeafInjection (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : daec_ForestLeafInjection ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_distinctArmEnds ω n h

lemma daec_forestLeafInjection_of_disjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hdisj : bk2_DisjointArmEnds ω n) :
    daec_ForestLeafInjection ω n :=
  bk2_distinctArmEnds_of_disjoint ω n hn hdisj

end Percolation

end StatMech
