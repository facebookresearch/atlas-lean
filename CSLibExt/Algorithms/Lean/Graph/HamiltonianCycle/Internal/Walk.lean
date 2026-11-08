/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Internal.Order
import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Internal.Validation
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!+# Private canonical Hamiltonian-cycle bridge

The source ordering is converted with Mathlib `Walk.ofSupport`. Closing uses
the existing path-append cycle theorem, not another walk or cycle predicate.
-/

namespace Cslib.Algorithms.Lean.Graph

lemma head_notMem_tail {α : Type} (vs : List α) (hne : vs ≠ [])
    (hnd : vs.Nodup) : vs.head hne ∉ vs.tail := by
  cases vs with
  | nil => exact (hne rfl).elim
  | cons a as => exact hnd.notMem

lemma closing_disjoint (m : Nat) (G : SimpleGraph (Fin m)) (vs : List (Fin m))
    (hne : vs ≠ []) (hnd : vs.Nodup) (hch : vs.IsChain G.Adj)
    (he : G.Adj (vs.getLast hne) (vs.head hne)) :
    (SimpleGraph.Walk.ofSupport vs hne hch).support.tail.Disjoint
      (SimpleGraph.Walk.cons he .nil).support.tail := by
  rw [SimpleGraph.Walk.support_ofSupport, SimpleGraph.Walk.support_cons,
    SimpleGraph.Walk.support_nil]
  simp only [List.tail_cons, List.disjoint_left, List.mem_singleton]
  intro a ha heq
  subst a
  exact head_notMem_tail vs hne hnd ha

lemma hamiltonianCycle_of_chain (m : Nat) (hm : 3 ≤ m) (G : SimpleGraph (Fin m))
    (vs : List (Fin m)) (hl : vs.length = m) (hnd : vs.Nodup)
    (hch : vs.IsChain G.Adj) (hne : vs ≠ [])
    (he : G.Adj (vs.getLast hne) (vs.head hne)) :
    ∃ v : Fin m, ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  let p := SimpleGraph.Walk.ofSupport vs hne hch
  let q : G.Walk (vs.getLast hne) (vs.head hne) := .cons he .nil
  have hp : p.IsPath := .mk' (by
    simpa only [p, SimpleGraph.Walk.support_ofSupport] using hnd)
  have hq : q.IsPath := .mk' (by simp [q, he.ne])
  have hd : p.support.tail.Disjoint q.support.tail := closing_disjoint m G vs hne hnd hch he
  have hpl : p.length = m - 1 := by
    simp only [p, SimpleGraph.Walk.length_ofSupport, hl]
  have hc : (p.append q).IsCycle := hp.isCycle_append hq hd (Or.inl (by omega))
  refine ⟨vs.head hne, p.append q,
    SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨hc, ?_⟩⟩
  simp only [SimpleGraph.Walk.length_append, hpl, q, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_nil, zero_add, Fintype.card_fin]
  omega

lemma hamiltonianCycle_of_order (m : Nat) (hm : 3 ≤ m) (G : SimpleGraph (Fin m))
    (f : Fin m → Fin m) (hf : Function.Injective f)
    (he : ∀ i : Fin m, G.Adj (f i)
      (f ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩)) :
    ∃ v : Fin m, ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  have hm' : 0 < m := by omega
  have hne : List.ofFn f ≠ [] := by
    intro h
    have hz := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at hz
    omega
  obtain ⟨a, b, ha, hb, he'⟩ := ofFn_closing_of_cycle_edges m hm' f he
  have hh := Option.some.inj ((List.head?_eq_some_head hne).symm.trans ha)
  have hl := Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hb)
  have hc : G.Adj ((List.ofFn f).getLast hne) ((List.ofFn f).head hne) := by
    rw [hh, hl]
    exact he'
  exact hamiltonianCycle_of_chain m hm G _ List.length_ofFn
    (ofFn_nodup_of_injective m f hf) (ofFn_chain_of_cycle_edges m hm' f he) hne hc

lemma graph_of_validated_array (x : Array Bool) (m : Nat)
    (hd : ∀ i : Fin m, x[i.val * m + i.val]? = some false)
    (hs : ∀ i j : Fin m, x[i.val * m + j.val]? = x[j.val * m + i.val]?) :
    ∃ G : SimpleGraph (Fin m),
      ∀ i j, G.Adj i j ↔ x[i.val * m + j.val]? = some true := by
  refine ⟨⟨fun i j => x[i.val * m + j.val]? = some true,
    ⟨fun i j h => (hs i j).symm.trans h⟩, ⟨fun i h => ?_⟩⟩, fun _ _ => Iff.rfl⟩
  rw [hd i] at h
  cases h

lemma validated_array_of_graph (x : Array Bool) (m : Nat) (G : SimpleGraph (Fin m))
    (hs : m * m = x.size)
    (hG : ∀ i j, G.Adj i j ↔ x[i.val * m + j.val]? = some true) :
    (validateGraph x m).ret = true := by
  have hr (i j : Fin m) := graph_read_some x (i.val * m + j.val)
    (lt_of_lt_of_eq (row_major_lt m i.val j.val i.isLt j.isLt) hs)
  apply (validateGraph_ret_iff_all x m).mpr
  refine ⟨hs, ?_, ?_⟩
  · intro i
    have hn : x[i.val * m + i.val]? ≠ some true := fun h => G.irrefl ((hG i i).mpr h)
    rw [hr i i] at hn
    cases h : x[i.val * m + i.val]?.getD false
    · rfl
    · exact (hn (congrArg some h)).elim
  · intro i j
    have he := (hG i j).symm.trans ((G.adj_comm i j).trans (hG j i))
    rw [hr i j, hr j i] at he
    cases h : x[i.val * m + j.val]?.getD false <;>
      cases h' : x[j.val * m + i.val]?.getD false <;> simp [h, h'] at he ⊢

lemma order_of_hamiltonianCycle (m : Nat) (G : SimpleGraph (Fin m))
    (v : Fin m) (p : G.Walk v v) (hp : p.IsHamiltonianCycle) :
    ∃ f : Fin m → Fin m, Function.Injective f ∧
      ∀ i : Fin m, G.Adj (f i)
        (f ⟨(i.val + 1) % m, Nat.mod_lt _ (by have := i.isLt; omega)⟩) := by
  cases p with
  | nil => exact (hp.ne_nil rfl).elim
  | cons h q =>
    have hnd : q.support.Nodup := by
      have hh := hp.isHamiltonian_tail.isPath.support_nodup
      rw [SimpleGraph.Walk.support_tail_of_not_nil _ hp.not_nil,
        SimpleGraph.Walk.support_cons, List.tail_cons] at hh
      exact hh
    have hl : q.support.length = m := by
      rw [SimpleGraph.Walk.length_support]
      simpa only [SimpleGraph.Walk.length_cons, Fintype.card_fin] using hp.length_eq
    let f : Fin m → Fin m := fun i => q.support[i.val]'(by rw [hl]; exact i.isLt)
    refine ⟨f, ?_, ?_⟩
    · intro i j hij
      exact Fin.ext (hnd.getElem_inj_iff.mp hij)
    · intro i
      have he : G.Adj (q.support.getLast q.support_ne_nil)
          (q.support.head q.support_ne_nil) := by
        simpa only [SimpleGraph.Walk.getLast_support, SimpleGraph.Walk.head_support] using h
      have hc := chain_closing_edges q.support q.isChain_adj_support
        (q.support.head q.support_ne_nil) (q.support.getLast q.support_ne_nil)
        (List.head?_eq_some_head q.support_ne_nil)
        (List.getLast?_eq_some_getLast q.support_ne_nil) he
        ⟨i.val, by rw [hl]; exact i.isLt⟩
      simpa only [hl, f] using hc

end Cslib.Algorithms.Lean.Graph
