/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.Percolation.FiniteTreeTripod
import Code.Walls.bc121trifcount

open Set SimpleGraph Finset

namespace StatMech.Percolation


private theorem tpt_degree_pos_of_connected {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    {x y : V} (hxy : x ≠ y) : 1 ≤ G.degree x := by
  have hr := hG.preconnected x y
  have hex : ∃ z, G.Adj x z := by
    obtain ⟨w⟩ := hr
    cases w with
    | nil => exact absurd rfl hxy
    | cons h _ => exact ⟨_, h⟩
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, G.degree_pos_iff_exists_adj]
  exact hex

private theorem tpt_degree_pos_of_reachable_ne {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    (hr : G.Reachable x y) (hxy : x ≠ y) : 1 ≤ G.degree x := by
  have hex : ∃ z, G.Adj x z := by
    obtain ⟨w⟩ := hr
    cases w with
    | nil => exact absurd rfl hxy
    | cons h _ => exact ⟨_, h⟩
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, G.degree_pos_iff_exists_adj]
  exact hex


private theorem tpt_degree_mono {V : Type*} [Fintype V]
    {F G : SimpleGraph V} [DecidableRel F.Adj] [DecidableRel G.Adj]
    (hFG : F ≤ G) (x : V) : F.degree x ≤ G.degree x := by
  rw [← F.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro y hy
  rw [SimpleGraph.mem_neighborFinset] at hy ⊢
  exact hFG hy





theorem three_pendant_vertices_have_tripod {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (p : Fin 3 → V) (hpinj : Function.Injective p)
    (hpdeg : ∀ i, G.degree (p i) = 1) :
    ∃ (C : Set V) (T : SimpleGraph C) (_ : DecidableRel T.Adj)
      (hub : C) (stem leaf : Fin 3 → C),
      T.IsTree ∧
      (∀ a b, T.Adj a b → G.Adj a.1 b.1) ∧
      Function.Injective stem ∧
      (∀ i, T.Adj hub (stem i)) ∧
      Function.Injective leaf ∧
      (∀ i, ∃ j, (leaf i).1 = p j) ∧
      (∀ i, (T.deleteIncidenceSet hub).Reachable (stem i) (leaf i)) ∧
      (∀ i, T.Reachable hub (leaf i)) ∧
      (∀ i j, i ≠ j →
        ¬ (T.deleteIncidenceSet hub).Reachable (leaf i) (leaf j)) := by
  classical
  obtain ⟨S, hSG, hStree⟩ := hG.exists_isTree_le
  letI : DecidableRel S.Adj := Classical.decRel _
  have hpSdeg : ∀ i, S.degree (p i) = 1 := by
    intro i
    have hj : ∃ j : Fin 3, i ≠ j := by
      fin_cases i
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    obtain ⟨j, hij⟩ := hj
    have hpne : p i ≠ p j := fun h => hij (hpinj h)
    have hlo : 1 ≤ S.degree (p i) :=
      tpt_degree_pos_of_connected S hStree.connected hpne
    have hhi : S.degree (p i) ≤ 1 := by
      rw [← hpdeg i]
      exact tpt_degree_mono hSG (p i)
    omega
  let B : V → Prop := fun v => ∃ i, p i = v
  letI : DecidablePred B := Classical.decPred _
  obtain ⟨F, hFdec, hFS, hFac, hFleaf, hFpres⟩ :=
    StatMech.Walls.bc121_boundaryAnchored_subforest S B hStree.isAcyclic
  letI : DecidableRel F.Adj := hFdec
  have hpFreach : ∀ i j, F.Reachable (p i) (p j) := by
    intro i j
    apply hFpres (p i) (p j) ⟨i, rfl⟩ ⟨j, rfl⟩
    exact hStree.connected.preconnected _ _
  have hpFdeg : ∀ i, F.degree (p i) = 1 := by
    intro i
    obtain ⟨j, hij⟩ : ∃ j : Fin 3, i ≠ j := by
      fin_cases i
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    have hpne : p i ≠ p j := fun h => hij (hpinj h)
    have hlo : 1 ≤ F.degree (p i) :=
      tpt_degree_pos_of_reachable_ne F (hpFreach i j) hpne
    have hhi : F.degree (p i) ≤ 1 := by
      rw [← hpSdeg i]
      exact tpt_degree_mono hFS (p i)
    omega
  let C : Set V := {v | F.Reachable (p 0) v}
  let T : SimpleGraph C := F.induce C
  have hpC : ∀ i, p i ∈ C := fun i => hpFreach 0 i
  have hCclosed : ∀ {x y : V}, F.Adj x y → x ∈ C → y ∈ C := by
    intro x y hxy hx
    exact hx.trans hxy.reachable
  have hTconn : T.Connected := by
    rw [connected_iff]
    refine ⟨?_, ⟨p 0, hpC 0⟩⟩
    intro a b
    obtain ⟨pa⟩ := a.2
    obtain ⟨pb⟩ := b.2
    let q := pa.reverse.append pb
    have hqC : ∀ x ∈ q.support, x ∈ C := by
      intro x hx
      exact ⟨pa.append (q.takeUntil x hx)⟩
    exact ⟨q.induce C hqC⟩
  have hTac : T.IsAcyclic := hFac.induce C
  have hTtree : T.IsTree := ⟨hTconn, hTac⟩
  have hTdegree (x : C) : T.degree x = F.degree x.1 := by
    change (F.induce C).degree x = F.degree x.1
    apply SimpleGraph.degree_induce_of_neighborSet_subset
    intro y hy
    exact hCclosed (SimpleGraph.mem_neighborSet F x.1 y |>.mp hy) x.2
  let pc : Fin 3 → C := fun i => ⟨p i, hpC i⟩
  have hpcinj : Function.Injective pc := fun i j h =>
    hpinj (congrArg Subtype.val h)
  have hpcdeg : ∀ i, T.degree (pc i) = 1 := by
    intro i
    rw [hTdegree]
    exact hpFdeg i
  obtain ⟨hub, hhub⟩ := ftt_branch_vertex_of_three_leaves T hTtree
    (fun h => (by decide : (0 : Fin 3) ≠ 1) (hpcinj h))
    (fun h => (by decide : (0 : Fin 3) ≠ 2) (hpcinj h))
    (fun h => (by decide : (1 : Fin 3) ≠ 2) (hpcinj h))
    (hpcdeg 0) (hpcdeg 1) (hpcdeg 2)
  obtain ⟨stem, leaf, hsteminj, hstemadj, hleafinj, hleafdeg,
      hstemleaf, hleafcut⟩ :=
    ftt_finite_tree_tripod_with_stems T hTtree hhub
  have hleaf_terminal : ∀ i, ∃ j, (leaf i).1 = p j := by
    intro i
    have hFdeg1 : F.degree (leaf i).1 = 1 := by
      rw [← hTdegree (leaf i)]
      exact hleafdeg i
    obtain ⟨j, hj⟩ := hFleaf (leaf i).1 hFdeg1
    exact ⟨j, hj.symm⟩
  refine ⟨C, T, inferInstance, hub, stem, leaf, hTtree, ?_, hsteminj,
    hstemadj, hleafinj, hleaf_terminal, hstemleaf, ?_, hleafcut⟩
  · intro a b hab
    exact hSG (hFS hab)
  · intro i
    exact hTtree.connected.preconnected _ _

end StatMech.Percolation
