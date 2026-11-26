/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Order.Filter.Defs
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GnBoundaryForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonForestCount

/-!
# Global forests on the contracted lattice

A finite forest carrying the contracted-lattice trifurcations as branch vertices, with leaves on the
boundary, bounds the coarse trifurcation count by the boundary size.

## i. Overview

`bc69_Gn_globalForest ω L R` asks for a finite acyclic graph on a set of sites without isolated
vertices, an injective placement of the contracted-lattice trifurcations of `B_R` as vertices of
degree at least three, and all leaves on the boundary of `B_R`. The branch–leaf inequality for
forests then gives `bc61_coarseTcount ≤ |∂B_R|`. Under translation invariance and finite-energy
merging, the forest for every configuration excludes `N = ∞`. In `bc60_upperLines` the coarse count
is controlled by an explicit forest.

The trifurcation notion here is the coarse one on `L`-boxes (`bc61_IsCoarseTrifurcation`,
`bc67_IsGnTrifurcation`), whose arms are infinite after the whole `L`-box is removed. Results that
assume a certificate for every configuration are conditional: no such certificate is constructed for
all configurations.

## ii. Key results

- `bc69_coarseTcount_le_boundary` : a global forest bounds the coarse count by the boundary size
- `bc69_globalForest_of_noTrif` : the forest exists when there is no contracted-lattice trifurcation
- `bc69_infiniteClusters_top_null_of_globalForest` : a global forest for every configuration
  excludes `N = ∞`
- `bc69_status` : the branch–leaf inequality and the counting bound together

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

lemma bc69_subtypeVal_injOn {p : Site d → Prop} (S : Set (Subtype p)) :
    Set.InjOn (Subtype.val : Subtype p → Site d) S :=
  Subtype.val_injective.injOn

/-- The origin lies in every box. See also `StatMech.FK.ocs_zero_mem_box`, the same statement. -/
lemma bc69_box_zero_mem (d R : ℕ) : (0 : Site d) ∈ box d R := by
  rw [mem_box]; intro i; simp

/-- The box `B_R` is nonempty: it contains the origin. -/
noncomputable instance bc69_boxNonempty (d R : ℕ) : Nonempty (↑(box d R) : Type) :=
  ⟨⟨0, bc69_box_zero_mem d R⟩⟩

/-- A global forest for box size `L` and box `B_R`: a finite forest without isolated vertices in
which the contracted-lattice trifurcations of `B_R` embed injectively with degree at least three
and whose leaves lie on the boundary of `B_R`. -/
def bc69_Gn_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type))
    (G : SimpleGraph (↑S : Type)) (_ : DecidableRel G.Adj) (ιU : Site d → (↑S : Type)),
    G.IsAcyclic ∧ (∀ v, 1 ≤ G.degree v) ∧
    (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y)) ∧
    (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) ∧
    (∀ v : (↑S : Type), G.degree v = 1 → (v : Site d) ∈ vertexBoundary d R)

lemma bc69_forestData_of_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) : bc68_GnForestData ω L R := by
  classical
  obtain ⟨S, hSfin, hSne, G, hGdec, ιU, hacyc, hmin, hdeg3, hιinj, hlammap⟩ := h
  refine ⟨(↑S : Type), hSfin, hSne, inferInstance, G, hGdec, ιU,
    (Subtype.val : (↑S : Type) → Site d), hacyc, hmin, hdeg3, hιinj, hlammap, ?_⟩
  exact bc69_subtypeVal_injOn _

lemma bc69_coarseTcount_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc68_coarseTcount_le_boundary_of_GnForestData ω L R (bc69_forestData_of_globalForest ω L R h)

lemma bc69_leaf_card_le_boundary_subtype (R : ℕ) {S : Set (Site d)} [Fintype (↑S : Type)]
    (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj]
    (hlammap : ∀ v : (↑S : Type), G.degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
    (univ.filter (fun v => G.degree v = 1)).card ≤ boxSV_boundaryCard d R :=
  flc2_leaf_card_le_boundary G R (Subtype.val : (↑S : Type) → Site d) hlammap
    (bc69_subtypeVal_injOn _)

lemma bc69_single_edge_degree {V : Type*} [Fintype V] [DecidableEq V] (a b : V) (hab : a ≠ b)
    [DecidableRel (SimpleGraph.fromEdgeSet {s(a,b)}).Adj] :
    (SimpleGraph.fromEdgeSet {s(a,b)}).degree a = 1 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  have hset : (Finset.univ.filter (fun w => (SimpleGraph.fromEdgeSet {s(a,b)}).Adj a w)) = {b} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro ⟨(⟨-, rfl⟩ | ⟨rfl, rfl⟩), hne⟩
      · rfl
      · exact absurd rfl hne
    · rintro rfl; exact ⟨by tauto, hab⟩
  rw [hset]; simp

lemma bc69_single_edge_degree_b {V : Type*} [Fintype V] [DecidableEq V] (a b : V) (hab : a ≠ b)
    [DecidableRel (SimpleGraph.fromEdgeSet {s(a,b)}).Adj] :
    (SimpleGraph.fromEdgeSet {s(a,b)}).degree b = 1 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  have hset : (Finset.univ.filter (fun w => (SimpleGraph.fromEdgeSet {s(a,b)}).Adj b w)) = {a} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro ⟨(⟨rfl, rfl⟩ | ⟨-, rfl⟩), hne⟩
      · exact absurd rfl hne
      · rfl
    · rintro rfl; exact ⟨by tauto, Ne.symm hab⟩
  rw [hset]; simp

lemma bc69_single_edge_acyclic {V : Type*} [DecidableEq V] (a b : V) (hab : a ≠ b) :
    (SimpleGraph.fromEdgeSet {s(a,b)}).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro u v huv
  rw [SimpleGraph.fromEdgeSet_adj] at huv
  obtain ⟨hmem, hne⟩ := huv
  simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
  rw [SimpleGraph.isBridge_iff]
  intro hreach
  obtain ⟨w⟩ := hreach
  have hbot : ((SimpleGraph.fromEdgeSet {s(a,b)}).deleteEdges {s(u, v)}) = ⊥ := by
    ext p q
    rw [SimpleGraph.deleteEdges_adj]
    simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff, SimpleGraph.bot_adj,
      iff_false, not_and]
    rintro ⟨hpq, hpqne⟩ hnpq
    apply hnpq
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hpq with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      subst_vars <;> tauto
  rw [hbot] at w
  exact hne (w.eq_of_length_eq_zero
    (by cases w with | nil => rfl | cons h _ => exact absurd h (by simp)))

open Classical in
lemma bc69_globalForest_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc69_Gn_globalForest ω L R := by
  classical
  set S : Set (Site d) := {z₀, z₁} with hS
  have hz₀S : z₀ ∈ S := by rw [hS]; left; rfl
  have hz₁S : z₁ ∈ S := by rw [hS]; right; rfl
  have hSfin : Fintype (↑S : Type) := (Set.toFinite S).fintype
  set a : (↑S : Type) := ⟨z₀, hz₀S⟩ with ha
  set b : (↑S : Type) := ⟨z₁, hz₁S⟩ with hb
  have hab : a ≠ b := by
    intro h; exact hzne (congrArg Subtype.val h)
  let G : SimpleGraph (↑S : Type) := SimpleGraph.fromEdgeSet {s(a, b)}
  have hGdec : DecidableRel G.Adj := Classical.decRel _
  have hVall : ∀ v : (↑S : Type), v = a ∨ v = b := by
    intro v
    obtain ⟨x, hx⟩ := v
    rw [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · left; rfl
    · right; rfl
  have hda : G.degree a = 1 := bc69_single_edge_degree a b hab
  have hdb : G.degree b = 1 := bc69_single_edge_degree_b a b hab
  refine ⟨S, hSfin, ⟨a⟩, G, hGdec, (fun _ => a), ?_, ?_, ?_, ?_, ?_⟩
  · exact bc69_single_edge_acyclic a b hab
  · intro v; rcases hVall v with rfl | rfl
    · rw [hda]
    · rw [hdb]
  · intro y hybox htri; exact absurd htri (hno y hybox)
  · intro y hybox htri; exact absurd htri (hno y hybox)
  · intro v _; rcases hVall v with rfl | rfl
    · exact hz₀
    · exact hz₁

lemma bc69_infiniteClusters_top_null_of_globalForest
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc68_infiniteClusters_top_null_of_GnForestData μ hd hinv hfe L
    (fun ω R => bc69_forestData_of_globalForest ω L R (hGlobal ω R)) hcoarseRoute

lemma bc69_upperLines_boundary_mem {R : ℕ} (hR3 : 4 ≤ R) (i : Fin 3) :
    bc57_pt (R : ℤ) ((i : ℤ) + 1) ∈ box 2 R := by
  rw [mem_box]; intro j; fin_cases j
  · change ((bc57_pt (R : ℤ) ((i : ℤ) + 1)) 0).natAbs ≤ R; rw [bc57_pt_fst]; simp
  · change ((bc57_pt (R : ℤ) ((i : ℤ) + 1)) 1).natAbs ≤ R; rw [bc57_pt_snd]
    fin_cases i <;> · push_cast; omega

lemma bc69_upperLines_globalForest_count {L R : ℕ}
    (h : bc69_Gn_globalForest bc60_upperLines L R) :
    bc61_coarseTcount bc60_upperLines L R ≤ boxSV_boundaryCard 2 R :=
  bc69_coarseTcount_le_boundary bc60_upperLines L R h

/-! ## B. Summary -/

lemma bc69_status :
    (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (univ.filter (fun v => 3 ≤ G.degree v)).card
        ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧
    (∀ (R : ℕ) (S : Set (↑(box d R) : Type)),
      Set.InjOn (Subtype.val : (↑(box d R) : Type) → Site d) S) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ G _ hacyc hmin
    exact Percolation.flc2_forest_internal_le_leaves G hacyc hmin
  · intro R S
    exact bc69_subtypeVal_injOn S
  · intro ω L R h
    exact bc69_coarseTcount_le_boundary ω L R h

end StatMech.Walls
