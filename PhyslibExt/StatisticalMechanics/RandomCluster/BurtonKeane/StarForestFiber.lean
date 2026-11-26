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
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifExploration

/-!
# Fibre forests and classical coarse explorations

Disjoint copies of an acyclic graph form a forest; leaf components with disjoint boundary contacts
give exploration certificates for classical coarse trifurcations.

## i. Overview

`bct_fiberForest β V H` is the disjoint union of `|β|` copies of `H`; it is acyclic when `H` is, and
degrees are those of `H`. The six-vertex double star `bct_dstarG` is a tree with two hubs of degree
three. A finite forest carrying the classical coarse trifurcations, whose leaves have disjoint
components meeting the boundary, gives `bfg_GenuineExploration` and the classical coarse count.

The trifurcation notion here is the classical one: three open neighbours whose clusters stay
infinite and pairwise disjoint after the centre is removed (`bc89_GenuineTrif`). For that notion the
counting bound is the classical deterministic Burton–Keane estimate; results that assume a
certificate for every configuration remain conditional on it.

## ii. Key results

- `bct_fiberForest_acyclic` : disjoint copies of an acyclic graph are acyclic
- `bct_dstarG_isTree` : the double star is a tree
- `bct_exploration_of_carrier` : a carrier forest gives an exploration certificate
- `bct_status` : the statements together

## iii. Table of contents

- A. Definitions
- B. Results
- C. Summary

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
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Definitions -/

/-- The disjoint union of copies of `H` indexed by `β`. -/
def bct_fiberForest (β V : Type) (H : SimpleGraph V) : SimpleGraph (β × V) :=
  SimpleGraph.fromRel (fun p q => p.1 = q.1 ∧ H.Adj p.2 q.2)

/-- Adjacency in the fibre forest is decidable. -/
noncomputable instance (β V : Type) (H : SimpleGraph V) : DecidableRel (bct_fiberForest β V H).Adj :=
  Classical.decRel _

/-! ## B. Results -/

lemma bct_fiberForest_adj_iff {β V : Type} {H : SimpleGraph V} {p q : β × V} :
    (bct_fiberForest β V H).Adj p q ↔ (p.1 = q.1 ∧ H.Adj p.2 q.2) := by
  unfold bct_fiberForest SimpleGraph.fromRel
  constructor
  · rintro ⟨hne, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨h1, h2⟩
    · exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun hpq => (H.ne_of_adj h2) (by rw [hpq]), Or.inl ⟨h1, h2⟩⟩

lemma bct_fiberForest_fst {β V : Type} {H : SimpleGraph V} {p q : β × V}
    (h : (bct_fiberForest β V H).Adj p q) : p.1 = q.1 := (bct_fiberForest_adj_iff.mp h).1

/-- The projection of the fibre forest onto `H`. -/
def bct_sndHom (β V : Type) (H : SimpleGraph V) : bct_fiberForest β V H →g H where
  toFun := Prod.snd
  map_rel' := fun h => (bct_fiberForest_adj_iff.mp h).2

lemma bct_walk_fst_const {β V : Type} {H : SimpleGraph V} {p q : β × V}
    (w : (bct_fiberForest β V H).Walk p q) : ∀ v ∈ w.support, v.1 = p.1 := by
  induction w with
  | nil => intro v hv; simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv; rw [hv]
  | @cons a b c hadj w' ih =>
    intro v hv
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · rfl
    · rw [ih v hv]; exact (bct_fiberForest_fst hadj).symm

lemma bct_snd_injOn_support {β V : Type} {H : SimpleGraph V} {v : β × V}
    (c : (bct_fiberForest β V H).Walk v v) :
    Set.InjOn (Prod.snd : β × V → V) {x | x ∈ c.support} := by
  intro a ha b hb hab
  exact Prod.ext ((bct_walk_fst_const c a ha).trans (bct_walk_fst_const c b hb).symm) hab

lemma bct_fiberForest_acyclic (β V : Type) (H : SimpleGraph V) (hH : H.IsAcyclic) :
    (bct_fiberForest β V H).IsAcyclic := by
  intro v c hc
  have hinj := bct_snd_injOn_support c
  have hcm : (c.map (bct_sndHom β V H)).IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def] at hc ⊢
    obtain ⟨htr, hne, hnodup⟩ := hc
    refine ⟨?_, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isTrail_def] at htr ⊢
      rw [SimpleGraph.Walk.edges_map]
      apply List.Nodup.map_on _ htr
      intro e1 he1 e2 he2 hee
      induction e1 using Sym2.ind with | _ a1 b1 =>
      induction e2 using Sym2.ind with | _ a2 b2 =>
      simp only [Sym2.map_mk] at hee
      have ha1 : a1 ∈ c.support := c.fst_mem_support_of_mem_edges he1
      have hb1 : b1 ∈ c.support := c.snd_mem_support_of_mem_edges he1
      have ha2 : a2 ∈ c.support := c.fst_mem_support_of_mem_edges he2
      have hb2 : b2 ∈ c.support := c.snd_mem_support_of_mem_edges he2
      rw [Sym2.eq_iff] at hee ⊢
      rcases hee with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · left; exact ⟨hinj ha1 ha2 e1, hinj hb1 hb2 e2⟩
      · right; exact ⟨hinj ha1 hb2 e1, hinj hb1 ha2 e2⟩
    · intro h
      apply hne
      cases c with
      | nil => rfl
      | cons hh w => simp [SimpleGraph.Walk.map_cons] at h
    · rw [SimpleGraph.Walk.support_map, ← List.map_tail]
      apply List.Nodup.map_on _ hnodup
      intro x hx y hy hxy
      exact hinj (List.mem_of_mem_tail hx) (List.mem_of_mem_tail hy) hxy
  exact hH (c.map (bct_sndHom β V H)) hcm

lemma bct_fiberForest_neighborFinset {β V : Type} [DecidableEq β] [Fintype β] [DecidableEq V]
    [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (t : β) (i : V) :
    (bct_fiberForest β V H).neighborFinset (t, i) = ({t} : Finset β) ×ˢ (H.neighborFinset i) := by
  classical
  ext ⟨t', j⟩
  simp only [SimpleGraph.mem_neighborFinset, bct_fiberForest_adj_iff, Finset.mem_product,
    Finset.mem_singleton]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩

lemma bct_fiberForest_degree {β V : Type} [DecidableEq β] [Fintype β] [DecidableEq V] [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (t : β) (i : V) :
    (bct_fiberForest β V H).degree (t, i) = H.degree i := by
  classical
  rw [SimpleGraph.degree, bct_fiberForest_neighborFinset, Finset.card_product,
    Finset.card_singleton, one_mul, SimpleGraph.degree]

/-- Edges of the six-vertex double star with hubs `0` and `1`. -/
def bct_dstarE (i j : Fin 6) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 1 ∧ j = 5)

/-- The double star relation is decidable. -/
instance : DecidableRel bct_dstarE := fun i j => by unfold bct_dstarE; infer_instance

/-- The six-vertex double star. -/
def bct_dstarG : SimpleGraph (Fin 6) := SimpleGraph.fromRel bct_dstarE

/-- Adjacency in the double star is decidable. -/
instance : DecidableRel bct_dstarG.Adj := by unfold bct_dstarG fromRel; intro a b; infer_instance

lemma bct_dstarG_isTree : bct_dstarG.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  exact ⟨by rw [SimpleGraph.connected_iff_exists_forall_reachable]; exact ⟨0, by decide⟩,
    by rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide⟩

lemma bct_dstarG_isAcyclic : bct_dstarG.IsAcyclic := bct_dstarG_isTree.isAcyclic

lemma bct_dstarG_hub0_deg : bct_dstarG.degree 0 = 3 := by decide

lemma bct_dstarG_hub1_deg : bct_dstarG.degree 1 = 3 := by decide

lemma bct_dstarG_leaf_deg : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → bct_dstarG.degree i = 1 := by decide

lemma bct_dstarG_min_deg : ∀ i : Fin 6, 1 ≤ bct_dstarG.degree i := by decide

lemma bct_dstarG_deg1_iff (i : Fin 6) : bct_dstarG.degree i = 1 ↔ (i ≠ 0 ∧ i ≠ 1) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro rfl; rw [bct_dstarG_hub0_deg] at h; exact absurd h (by decide)
    · rintro rfl; rw [bct_dstarG_hub1_deg] at h; exact absurd h (by decide)
  · exact fun ⟨h0, h1⟩ => bct_dstarG_leaf_deg i h0 h1

lemma bct_exploration_of_carrier (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (ιT : Site d → W) (comp : W → Set (Site d))
    (hacyc : G.IsAcyclic)
    (hmin : ∀ v, 1 ≤ G.degree v)
    (hdeg3 : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → 3 ≤ G.degree (ιT y))
    (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
      btr_IsGenuineCoarseTrif ω L z → ιT y = ιT z → y = z)
    (hbnd : ∀ v, G.degree v = 1 → (comp v ∩ vertexBoundary d R).Nonempty)
    (hdisj : ∀ u, G.degree u = 1 → ∀ v, G.degree v = 1 → u ≠ v → Disjoint (comp u) (comp v)) :
    bfg_GenuineExploration ω L R :=
  ⟨W, inferInstance, inferInstance, inferInstance, G, inferInstance, ιT, comp,
    hacyc, hmin, hdeg3, hinj, hbnd, hdisj⟩


open Classical in
lemma bct_exploration_of_twoSharedTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {y₀ y₁ : Site d} (hy0 : btr_IsGenuineCoarseTrif ω L y₀) (hy1 : btr_IsGenuineCoarseTrif ω L y₁)
    (hy0box : y₀ ∈ box d R) (hy1box : y₁ ∈ box d R) (hne : y₀ ≠ y₁)
    (huniq : ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → z = y₀ ∨ z = y₁)
    (comp : Fin 6 → Set (Site d))
    (hcompB : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → (comp i ∩ vertexBoundary d R).Nonempty)
    (hcompD : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → ∀ j : Fin 6, j ≠ 0 → j ≠ 1 → i ≠ j →
      Disjoint (comp i) (comp j)) :
    bfg_GenuineExploration ω L R := by
  classical
  let ιT : Site d → Fin 6 := fun z => if z = y₀ then 0 else if z = y₁ then 1 else 0
  have hιT0 : ιT y₀ = 0 := by simp [ιT]
  have hιT1 : ιT y₁ = 1 := by simp [ιT, (Ne.symm hne)]
  refine bct_exploration_of_carrier ω L R (Fin 6) bct_dstarG ιT comp
    bct_dstarG_isAcyclic bct_dstarG_min_deg ?_ ?_ ?_ ?_
  · intro z hzbox hzgen
    rcases huniq z hzbox hzgen with rfl | rfl
    · rw [hιT0, bct_dstarG_hub0_deg]
    · rw [hιT1, bct_dstarG_hub1_deg]
  · intro z hzbox hzgen z' hz'box hz'gen hzz
    rcases huniq z hzbox hzgen with rfl | rfl <;>
      rcases huniq z' hz'box hz'gen with rfl | rfl
    · rfl
    · rw [hιT0, hιT1] at hzz; exact absurd hzz (by decide)
    · rw [hιT0, hιT1] at hzz; exact absurd hzz.symm (by decide)
    · rfl
  · intro v hv
    rw [bct_dstarG_deg1_iff] at hv
    exact hcompB v hv.1 hv.2
  · intro u hu v hv huv
    rw [bct_dstarG_deg1_iff] at hu hv
    exact hcompD u hu.1 hu.2 v hv.1 hv.2 huv

lemma bct_genuineForest_of_carrier (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (ιT : Site d → W) (comp : W → Set (Site d))
    (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (hdeg3 : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → 3 ≤ G.degree (ιT y))
    (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
      btr_IsGenuineCoarseTrif ω L z → ιT y = ιT z → y = z)
    (hbnd : ∀ v, G.degree v = 1 → (comp v ∩ vertexBoundary d R).Nonempty)
    (hdisj : ∀ u, G.degree u = 1 → ∀ v, G.degree v = 1 → u ≠ v → Disjoint (comp u) (comp v)) :
    bgt_GenuineForest ω L R :=
  bfg_genuineForest_of_exploration ω L R
    (bct_exploration_of_carrier ω L R W G ιT comp hacyc hmin hdeg3 hinj hbnd hdisj)

lemma bct_genuineTcount_of_carrier (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (ιT : Site d → W) (comp : W → Set (Site d))
    (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (hdeg3 : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → 3 ≤ G.degree (ιT y))
    (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
      btr_IsGenuineCoarseTrif ω L z → ιT y = ιT z → y = z)
    (hbnd : ∀ v, G.degree v = 1 → (comp v ∩ vertexBoundary d R).Nonempty)
    (hdisj : ∀ u, G.degree u = 1 → ∀ v, G.degree v = 1 → u ≠ v → Disjoint (comp u) (comp v)) :
    (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R :=
  bgt_genuineTcount_le_boundary ω L R
    (bct_genuineForest_of_carrier ω L R W G ιT comp hacyc hmin hdeg3 hinj hbnd hdisj)

lemma bct_twoSharedTrif_genuineForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {y₀ y₁ : Site d} (hy0 : btr_IsGenuineCoarseTrif ω L y₀) (hy1 : btr_IsGenuineCoarseTrif ω L y₁)
    (hy0box : y₀ ∈ box d R) (hy1box : y₁ ∈ box d R) (hne : y₀ ≠ y₁)
    (huniq : ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → z = y₀ ∨ z = y₁)
    (comp : Fin 6 → Set (Site d))
    (hcompB : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → (comp i ∩ vertexBoundary d R).Nonempty)
    (hcompD : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → ∀ j : Fin 6, j ≠ 0 → j ≠ 1 → i ≠ j →
      Disjoint (comp i) (comp j)) :
    bgt_GenuineForest ω L R :=
  bfg_genuineForest_of_exploration ω L R
    (bct_exploration_of_twoSharedTrif ω L R hy0 hy1 hy0box hy1box hne huniq comp hcompB hcompD)

lemma bct_genuineTcount_of_connectedTree (L R : ℕ)
    (hexpl : ∀ ω : ConfigSpace (Sym2 (Site d)), bfg_GenuineExploration ω L R) :
    ∀ ω : ConfigSpace (Sym2 (Site d)),
      (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R :=
  fun ω => bfg_genuineTcount_le_boundary ω L R (hexpl ω)

/-! ## C. Summary -/

lemma bct_status :
    (∀ (β V : Type) (H : SimpleGraph V), H.IsAcyclic → (bct_fiberForest β V H).IsAcyclic) ∧
    bct_dstarG.IsTree ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (W : Type) [Fintype W] [Nonempty W]
      [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
      (ιT : Site d → W) (comp : W → Set (Site d)),
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → 3 ≤ G.degree (ιT y)) →
      (∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
        btr_IsGenuineCoarseTrif ω L z → ιT y = ιT z → y = z) →
      (∀ v, G.degree v = 1 → (comp v ∩ vertexBoundary d R).Nonempty) →
      (∀ u, G.degree u = 1 → ∀ v, G.degree v = 1 → u ≠ v → Disjoint (comp u) (comp v)) →
      bfg_GenuineExploration ω L R) ∧
    (∀ (L R : ℕ), (∀ ω : ConfigSpace (Sym2 (Site d)), bfg_GenuineExploration ω L R) →
      ∀ ω : ConfigSpace (Sym2 (Site d)),
        (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R) := by
  refine ⟨fun β V H hH => bct_fiberForest_acyclic β V H hH, bct_dstarG_isTree, ?_, ?_⟩
  · intro ω L R W _ _ _ G _ ιT comp hacyc hmin hdeg3 hinj hbnd hdisj
    exact bct_exploration_of_carrier ω L R W G ιT comp hacyc hmin hdeg3 hinj hbnd hdisj
  · intro L R hexpl ω
    exact bct_genuineTcount_of_connectedTree L R hexpl ω

end StatMech.Walls
