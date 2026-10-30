/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedHubContraction
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalForestLeafCount

/-!
# Disjoint star forests

A graph homomorphism to an acyclic graph that is injective on cycles shows acyclicity; leaves of the
disjoint star lie inside the box, and separated arm graphs hold for `L ≥ 3`.

## i. Overview

If `f : G →g H` with `H` acyclic is injective on the support of every cycle of `G`, then `G` is
acyclic. The leaves of the disjoint star are interior to the box of radius `R ≥ 2`, and the
separated arm graph holds for `L ≥ 3`.

## ii. Key results

- `bfc_acyclic_of_walkInjHom` : acyclicity through a homomorphism injective on cycles.

## iii. Table of contents

- A. Acyclicity and stars

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

variable {d : ℕ}

open StatMech.Percolation

/-! ## A. Acyclicity and stars -/

lemma bfc_acyclic_of_walkInjHom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hH : H.IsAcyclic)
    (hinj : ∀ {v : V} (c : G.Walk v v), c.IsCycle →
      Set.InjOn f {x | x ∈ c.support}) :
    G.IsAcyclic := by
  intro v c hc
  have hinjc := hinj c hc
  have hcm : (c.map f).IsCycle := by
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
      · left; exact ⟨hinjc ha1 ha2 e1, hinjc hb1 hb2 e2⟩
      · right; exact ⟨hinjc ha1 hb2 e1, hinjc hb1 ha2 e2⟩
    · intro h
      apply hne
      cases c with
      | nil => rfl
      | cons hh w => simp [SimpleGraph.Walk.map_cons] at h
    · rw [SimpleGraph.Walk.support_map, ← List.map_tail]
      apply List.Nodup.map_on _ hnodup
      intro x hx y hy hxy
      exact hinjc (List.mem_of_mem_tail hx) (List.mem_of_mem_tail hy) hxy
  exact hH (c.map f) hcm

lemma bfc_disjointStar_leaves_interior (hd : 1 ≤ d) {R : ℕ} (hR : 2 ≤ R) :
    bc112_leaf hd (0 : Site d) 1 ∉ vertexBoundary d R := by
  rw [vertexBoundary, Set.mem_sdiff, not_and_or, not_not]
  right
  rw [mem_box]
  intro i
  by_cases hi : i = ⟨0, hd⟩
  · subst hi
    rw [bc112_leaf_coord0]
    simp only [Pi.zero_apply, zero_add]
    rw [Int.natAbs_one]; omega
  · rw [bc112_leaf_coord_ne hd (0 : Site d) 1 hi]
    simp

lemma bfc_gap1_free (hd : 1 ≤ d) (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hL : 3 ≤ L) :
    bc112_SeparatedArmGraph ω L R :=
  bc112_separatedArmGraph_holds hd ω L R hL

lemma bfc_status (hd : 1 ≤ d) :
    (∀ (β : Type), (bc64_starForest β).IsAcyclic) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 3 ≤ L → bc112_SeparatedArmGraph ω L R) ∧
    (∀ {R : ℕ}, 2 ≤ R → bc112_leaf hd (0 : Site d) 1 ∉ vertexBoundary d R) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      (∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) → bc69_Gn_globalForest ω L R) := by
  refine ⟨StatMech.Walls.bc64_starForest_acyclic, ?_, ?_, ?_⟩
  · intro ω L R hL; exact bfc_gap1_free hd ω L R hL
  · intro R hR; exact bfc_disjointStar_leaves_interior hd hR
  · intro ω L R z₀ z₁ hz₀ hz₁ hzne hno; exact StatMech.Walls.bc102_connectedForest_of_noTrif ω L R
      hz₀ hz₁ hzne hno

end StatMech.Walls
