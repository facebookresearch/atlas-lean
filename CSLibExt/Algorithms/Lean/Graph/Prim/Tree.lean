/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.Prim.Basic
import all CSLibExt.Algorithms.Lean.Graph.Prim.QueueInvariants
import all CSLibExt.Algorithms.Lean.Graph.Prim.ParentInvariants
import all CSLibExt.Algorithms.Lean.Graph.Prim.CutInvariants
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Prim parent-tree correctness from actual extraction ranks

Adapted from CLRS, fourth edition, section 21.2, Prim's algorithm.
Proofs and executable code authored with Codex under Adam Kiezun's authorization.
-/

open Cslib.Algorithms.Lean

namespace Cslib.Algorithms.Lean.Prim

private lemma parent_rank_isTree {n : Nat}
    (parents : Vector (Option (Fin n)) n) (root : Fin n) (rank : Fin n → Nat) :
    parents[root] = none →
      (∀ v : Fin n, v ≠ root → ∃ p : Fin n, parents[v] = some p) →
      (∀ v p : Fin n, parents[v] = some p → rank p < rank v) →
        (SimpleGraph.fromRel (fun u v : Fin n => parents[v] = some u)).IsTree := by
  classical
  intro hroot htotal hrank
  let : Nonempty (Fin n) := ⟨root⟩
  let G := SimpleGraph.fromRel (fun u v : Fin n => parents[v] = some u)
  change G.IsTree
  let parent : {v : Fin n // v ≠ root} → Fin n := fun v =>
    Classical.choose (htotal v v.property)
  have hparent (v : {v : Fin n // v ≠ root}) : parents[(v : Fin n)] = some (parent v) :=
    Classical.choose_spec (htotal v v.property)
  have reaches_root : ∀ v : Fin n, G.Reachable v root := by
    intro v
    generalize hv : rank v = k
    induction k using Nat.strong_induction_on generalizing v with
    | h k ih =>
      by_cases hvr : v = root
      · subst v
        exact .refl root
      · let v' : {x : Fin n // x ≠ root} := ⟨v, hvr⟩
        have hvp := hparent v'
        have hpv := hrank v (parent v') hvp
        have hpk : rank (parent v') < k := by omega
        have hadj : G.Adj v (parent v') := by
          change (SimpleGraph.fromRel
            (fun u w : Fin n => parents[w] = some u)).Adj v (parent v')
          rw [SimpleGraph.fromRel_adj]
          exact ⟨fun he => lt_irrefl _
            (hpv.trans_le (le_of_eq (congrArg rank he))), Or.inr hvp⟩
        exact hadj.reachable.trans (ih _ hpk _ rfl)
  have hconnected : G.Connected := by
    refine SimpleGraph.Connected.mk ?_
    intro u v
    exact (reaches_root u).trans (reaches_root v).symm
  let edgeMap : {v : Fin n // v ≠ root} → G.edgeSet := fun v =>
    ⟨s((v : Fin n), parent v), by
      change G.Adj v (parent v)
      change (SimpleGraph.fromRel
        (fun u w : Fin n => parents[w] = some u)).Adj v (parent v)
      rw [SimpleGraph.fromRel_adj]
      exact ⟨fun he => lt_irrefl _
        ((hrank v (parent v) (hparent v)).trans_le
          (le_of_eq (congrArg rank he))), Or.inr (hparent v)⟩⟩
  have edgeMap_injective : Function.Injective edgeMap := by
    intro v w hvw
    apply Subtype.ext
    have h := congrArg Subtype.val hvw
    change s((v : Fin n), parent v) = s((w : Fin n), parent w) at h
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
    rcases h with h | h
    · exact h.1
    · have hv := hrank v (parent v) (hparent v)
      have hw := hrank w (parent w) (hparent w)
      have hforward := hv.trans_le (le_of_eq (congrArg rank h.1))
      have hbackward := hw.trans_le (le_of_eq (congrArg rank h.2.symm))
      exact False.elim (lt_asymm hforward hbackward)
  have edgeMap_surjective : Function.Surjective edgeMap := by
    rintro ⟨e, he⟩
    revert he
    refine Sym2.ind ?_ e
    intro a b hab
    change G.Adj a b at hab
    change (SimpleGraph.fromRel
      (fun u w : Fin n => parents[w] = some u)).Adj a b at hab
    rw [SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with hp | hp
    · have hbnr : b ≠ root := by
        intro hbr
        subst b
        rw [hroot] at hp
        contradiction
      let vb : {v : Fin n // v ≠ root} := ⟨b, hbnr⟩
      have hpa : parent vb = a := by
        have hpb : parents[b] = some (parent vb) := hparent vb
        exact Option.some.inj (hpb.symm.trans hp)
      refine ⟨vb, Subtype.ext ?_⟩
      change s((vb : Fin n), parent vb) = s(a, b)
      rw [hpa, Sym2.eq_swap]
    · have hanr : a ≠ root := by
        intro har
        subst a
        rw [hroot] at hp
        contradiction
      let va : {v : Fin n // v ≠ root} := ⟨a, hanr⟩
      have hpb : parent va = b := by
        have hpa : parents[a] = some (parent va) := hparent va
        exact Option.some.inj (hpa.symm.trans hp)
      refine ⟨va, Subtype.ext ?_⟩
      change s((va : Fin n), parent va) = s(a, b)
      rw [hpb]
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconnected, ?_⟩
  let edgeEquiv : {v : Fin n // v ≠ root} ≃ G.edgeSet :=
    Equiv.ofBijective edgeMap ⟨edgeMap_injective, edgeMap_surjective⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← Fintype.card_congr edgeEquiv]
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have hcard : Fintype.card {v : Fin n // v ≠ root} = n - 1 := by simp
  rw [hcard, Fintype.card_fin]
  omega

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

universe uptree1

private lemma prim_parent_graph_isTree {W : Type uptree1} [LinearOrder W] [Zero W]
    {n : Nat} (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (root : Fin n) (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (hadj : ∀ u v : Fin n, v ∈ graph.adjacency u ↔ G.Adj u v) :
    (SimpleGraph.fromRel
      (fun u v : Fin n => (worker graph weight root).ret.parent[v] = some u)).IsTree := by
  apply parent_rank_isTree (worker graph weight root).ret.parent root
    (fun v => (worker graph weight root).ret.extracted.length -
      ((worker graph weight root).ret.extracted.map Prod.snd).idxOf v)
  · exact prim_root_parent graph weight root
  · exact prim_parent_total_of_connected graph weight root G hG hadj
  · intro v p hp
    exact prim_parent_rank graph weight root v p hp

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

end Cslib.Algorithms.Lean.Prim
