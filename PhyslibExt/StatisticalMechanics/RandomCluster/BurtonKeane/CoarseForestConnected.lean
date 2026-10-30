/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseStarForestEmbedding
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonForestCount

/-!
# Connected coarse forests and caterpillars

The connected coarse forest is the coarse arm embedding and bounds the coarse count; caterpillar
trees show that the leaf count of a forest can be well below three times its branch vertices.

## i. Overview

`bc65_ConnectedCoarseForest` is defined as the coarse forest leaf count, so it is the coarse arm
embedding and bounds the coarse count. In a forest of minimum degree one, branch vertices are at
most leaves. The caterpillars `bc65_cat2G` (two spine vertices) and `bc65_cat3G` (three) are trees
with fewer than three leaves per branch vertex. Boundary injections, forest data and two-hub
caterpillars give connected forests, and with the coarse step the connected forest gives
`μ(N = ⊤) = 0`.

## ii. Key results

- `bc65_coarseTcount_le_boundary_of_connectedForest` : the coarse count from the connected forest.
- `bc65_caterpillar2_savings` : a caterpillar with fewer than three leaves per branch vertex.

## iii. Table of contents

- A. Connected coarse forests
- B. Caterpillars
- C. Constructions

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Connected coarse forests -/

/-- The connected coarse forest condition, defined as the coarse forest leaf count
`bc61_CoarseForestLeafCount`. Same statement as `bc63_CoarseArmEmbedding`; kept because
GnBoundaryForest, TrifSuperVertex use it. -/
def bc65_ConnectedCoarseForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  bc61_CoarseForestLeafCount ω L R

lemma bc65_connectedCoarseForest_iff_armEmbedding (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    bc65_ConnectedCoarseForest ω L R ↔ bc63_CoarseArmEmbedding ω L R :=
  Iff.rfl

lemma bc65_coarseArmEmbedding_of_connectedForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc65_ConnectedCoarseForest ω L R) : bc63_CoarseArmEmbedding ω L R :=
  (bc65_connectedCoarseForest_iff_armEmbedding ω L R).mp h

lemma bc65_coarseTcount_le_boundary_of_connectedForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc65_ConnectedCoarseForest ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc63_coarseTcount_le_boundary_of_armEmbedding ω L R
    (bc65_coarseArmEmbedding_of_connectedForest ω L R h)

lemma bc65_connected_leaf_count {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      ≤ (univ.filter (fun v => G.degree v = 1)).card :=
  flc2_forest_internal_le_leaves G hacyc hmin

/-! ## B. Caterpillars -/

/-- Edges of the caterpillar on `Fin 6` with spine `0 — 1`. -/
def bc65_cat2E (a b : Fin 6) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
  (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨
  (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) ∨
  (a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1) ∨
  (a = 1 ∧ b = 5) ∨ (a = 5 ∧ b = 1)

/-- `bc65_cat2E` is decidable. -/
instance : DecidableRel bc65_cat2E := fun a b => by unfold bc65_cat2E; infer_instance

/-- The caterpillar tree on `Fin 6` with spine `0 — 1`. -/
def bc65_cat2G : SimpleGraph (Fin 6) := SimpleGraph.fromRel bc65_cat2E

/-- Adjacency in `bc65_cat2G` is decidable. -/
instance : DecidableRel bc65_cat2G.Adj := by unfold bc65_cat2G fromRel; intro a b; infer_instance

lemma bc65_cat2G_isTree : bc65_cat2G.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]; exact ⟨0, by decide⟩
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide

lemma bc65_caterpillar2_leafCount :
    (univ.filter (fun v => 3 ≤ bc65_cat2G.degree v)).card = 2 ∧
    (univ.filter (fun v => bc65_cat2G.degree v = 1)).card = 4 := by
  constructor <;> decide

lemma bc65_caterpillar2_savings :
    (univ.filter (fun v => bc65_cat2G.degree v = 1)).card
      < 3 * (univ.filter (fun v => 3 ≤ bc65_cat2G.degree v)).card := by
  rw [bc65_caterpillar2_leafCount.1, bc65_caterpillar2_leafCount.2]; norm_num

/-- Edges of the caterpillar on `Fin 8` with spine `2 — 1 — 0`. -/
def bc65_cat3E (a b : Fin 8) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
  (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨
  (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) ∨
  (a = 0 ∧ b = 6) ∨ (a = 6 ∧ b = 0) ∨
  (a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1) ∨
  (a = 2 ∧ b = 5) ∨ (a = 5 ∧ b = 2) ∨
  (a = 2 ∧ b = 7) ∨ (a = 7 ∧ b = 2)

/-- `bc65_cat3E` is decidable. -/
instance : DecidableRel bc65_cat3E := fun a b => by unfold bc65_cat3E; infer_instance

/-- The caterpillar tree on `Fin 8` with a spine of three vertices. -/
def bc65_cat3G : SimpleGraph (Fin 8) := SimpleGraph.fromRel bc65_cat3E

/-- Adjacency in `bc65_cat3G` is decidable. -/
instance : DecidableRel bc65_cat3G.Adj := by unfold bc65_cat3G fromRel; intro a b; infer_instance

lemma bc65_cat3G_isTree : bc65_cat3G.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]; exact ⟨0, by decide⟩
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide

lemma bc65_cat3G_leafCount :
    (univ.filter (fun v => 3 ≤ bc65_cat3G.degree v)).card = 3 ∧
    (univ.filter (fun v => bc65_cat3G.degree v = 1)).card = 5 := by
  constructor <;> decide

lemma bc65_cat3G_savings :
    (univ.filter (fun v => bc65_cat3G.degree v = 1)).card
      < 3 * (univ.filter (fun v => 3 ≤ bc65_cat3G.degree v)).card := by
  rw [bc65_cat3G_leafCount.1, bc65_cat3G_leafCount.2]; norm_num

/-! ## C. Constructions -/

lemma bc65_connectedForest_of_boundaryInjection (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hinj : bc64_CoarseBoundaryInjection ω L R) :
    bc65_ConnectedCoarseForest ω L R :=
  bc64_coarseArmEmbedding_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj

set_option linter.unusedDecidableInType false in
lemma bc65_connectedForest_of_forestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (ιT : Site d → W) (lamL : W → Site d)
    (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (hdeg3 : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → 3 ≤ G.degree (ιT y))
    (hιinj : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc61_IsCoarseTrifurcation ω L z → ιT y = ιT z → y = z)
    (hlammap : ∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d R)
    (hlaminj : Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))) :
    bc65_ConnectedCoarseForest ω L R :=
  ⟨W, inferInstance, inferInstance, inferInstance, G, inferInstance, ιT, lamL,
    hacyc, hmin, hdeg3, hιinj, hlammap, hlaminj⟩

lemma bc65_cat2G_min_degree : ∀ v : Fin 6, 1 ≤ bc65_cat2G.degree v := by decide

lemma bc65_cat3G_min_degree : ∀ v : Fin 8, 1 ≤ bc65_cat3G.degree v := by decide

lemma bc65_connectedForest_caterpillar2 (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {y₀ y₁ : Site d} (_hy₀box : y₀ ∈ box d R) (_hy₁box : y₁ ∈ box d R) (_hyne : y₀ ≠ y₁)
    (_hy₀tri : bc61_IsCoarseTrifurcation ω L y₀) (_hy₁tri : bc61_IsCoarseTrifurcation ω L y₁)
    (hpair : ∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → y = y₀ ∨ y = y₁)
    (lamL : Fin 6 → Site d)
    (hlammap : ∀ v, bc65_cat2G.degree v = 1 → lamL v ∈ vertexBoundary d R)
    (hlaminj : Set.InjOn lamL (univ.filter (fun v => bc65_cat2G.degree v = 1))) :
    bc65_ConnectedCoarseForest ω L R := by
  classical
  refine bc65_connectedForest_of_forestData ω L R (Fin 6) bc65_cat2G
    (fun y => if y = y₀ then 0 else 1) lamL bc65_cat2G_isTree.isAcyclic bc65_cat2G_min_degree
    ?_ ?_ hlammap hlaminj
  · intro y hybox htri
    by_cases hy : y = y₀
    · rw [ite_eq_left hy]; decide
    · rw [ite_eq_right hy]; decide
  · intro y hybox htri z hzbox htriz hyz
    replace hyz : (if y = y₀ then (0 : Fin 6) else 1) = (if z = y₀ then 0 else 1) := hyz
    by_cases hyy₀ : y = y₀ <;> by_cases hzy₀ : z = y₀
    · rw [hyy₀, hzy₀]
    · rw [ite_eq_left hyy₀, ite_eq_right hzy₀] at hyz; exact absurd hyz (by decide)
    · rw [ite_eq_right hyy₀, ite_eq_left hzy₀] at hyz; exact absurd hyz (by decide)
    · have hy1 : y = y₁ := (hpair y hybox htri).resolve_left hyy₀
      have hz1 : z = y₁ := (hpair z hzbox htriz).resolve_left hzy₀
      rw [hy1, hz1]

lemma bc65_infiniteClusters_top_null_of_connectedForest_route
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hconn : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc65_ConnectedCoarseForest ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc63_infiniteClusters_top_null_of_armEmbedding_route μ hd hinv hfe L
    (fun ω R => bc65_coarseArmEmbedding_of_connectedForest ω L R (hconn ω R)) hcoarseRoute

lemma bc65_status :
    (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (univ.filter (fun v => 3 ≤ G.degree v)).card
        ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧
    ((univ.filter (fun v => bc65_cat2G.degree v = 1)).card
        < 3 * (univ.filter (fun v => 3 ≤ bc65_cat2G.degree v)).card) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc65_ConnectedCoarseForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      bc64_CoarseBoundaryInjection ω L R → bc65_ConnectedCoarseForest ω L R) := by
  refine ⟨?_, bc65_caterpillar2_savings, ?_, ?_⟩
  · intro V _ _ G _ hacyc hmin
    exact bc65_connected_leaf_count G hacyc hmin
  · intro ω L R h
    exact bc65_coarseTcount_le_boundary_of_connectedForest ω L R h
  · intro ω L R z₀ z₁ hz₀ hz₁ hzne hinj
    exact bc65_connectedForest_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj

end StatMech.Walls
