/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import MathlibExt.Combinatorics.SimpleGraph.EdgeColoring
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic.Push

@[expose] public section

section
namespace MathlibExt.Combinatorics.SimpleGraph.EdgeColoringWanted

/-!
# Edge coloring landmarks

Records Vizing and König edge-coloring theorems.
-/

-- `IsProperEdgeColoring`, `IsProperSym2Coloring`, and the bridge/mono lemmas
-- are imported from `EdgeColoring` in the same namespace.

/-- Colors missing at a vertex. -/
private noncomputable def missingColors {V K : Type*} [Fintype K] [DecidableEq K]
    (G : _root_.SimpleGraph V)
    (c : Sym2 V → K) (u : V) : Finset K := by
  classical
  exact Finset.univ.filter (fun i => ∀ (y : V), G.Adj u y → c s(u, y) ≠ i)

private theorem mem_missingColors_iff {V K : Type*} [Fintype K] [DecidableEq K]
    {G : _root_.SimpleGraph V}
    {c : Sym2 V → K} {u : V} {i : K} :
    i ∈ missingColors G c u ↔ ∀ (y : V), G.Adj u y → c s(u, y) ≠ i := by
  classical
  simp [missingColors]

/-- Kempe swap: swap colors α β on pairs fully inside S. -/
private noncomputable def kempeSwap {V K : Type*} [DecidableEq K]
    (c : Sym2 V → K) (α β : K) (S : Set V) : Sym2 V → K :=
  open Classical in
  fun e => if ∀ x ∈ e, x ∈ S then Equiv.swap α β (c e) else c e

private theorem kempeSwap_apply_of_mem {V K : Type*} [DecidableEq K]
    {G : _root_.SimpleGraph V} {c : Sym2 V → K} {α β : K} {S : Set V}
    (hclosed : ∀ {x y : V}, x ∈ S → G.Adj x y → (c s(x, y) = α ∨ c s(x, y) = β) → y ∈ S)
    {x y : V} (h : G.Adj x y) (hx : x ∈ S) :
    kempeSwap c α β S s(x, y) = Equiv.swap α β (c s(x, y)) := by
  have hall_or : (∀ x_1 ∈ s(x, y), x_1 ∈ S) ∨ ¬ ∀ x_1 ∈ s(x, y), x_1 ∈ S := Classical.em _
  rcases hall_or with hall | hhall
  · simp only [kempeSwap]
    rw [ite_eq_left hall]
  · have hy : y ∉ S := by
      intro hyS
      exact hhall (fun a ha => by rw [Sym2.mem_iff] at ha; rcases ha with rfl | rfl <;> assumption)
    have hne1 : c s(x, y) ≠ α := fun heq => hy (hclosed hx h (Or.inl heq))
    have hne2 : c s(x, y) ≠ β := fun heq => hy (hclosed hx h (Or.inr heq))
    simp only [kempeSwap]
    rw [ite_eq_right hhall]
    exact (Equiv.swap_apply_of_ne_of_ne hne1 hne2).symm

private theorem kempeSwap_apply_of_notMem {V K : Type*} [DecidableEq K]
    {G : _root_.SimpleGraph V} {c : Sym2 V → K} {α β : K} {S : Set V}
    {x y : V} (_h : G.Adj x y) (hx : x ∉ S) :
    kempeSwap c α β S s(x, y) = c s(x, y) := by
  have hhall : ¬ ∀ x_1 ∈ s(x, y), x_1 ∈ S := by
    intro hall
    exact hx (hall x (Sym2.mem_mk_left x y))
  simp only [kempeSwap]
  rw [ite_eq_right hhall]

private theorem isProperSym2Coloring_kempeSwap {V K : Type*} [DecidableEq K]
    {G : _root_.SimpleGraph V} {c : Sym2 V → K} (hc : IsProperSym2Coloring G c)
    {α β : K} {S : Set V}
    (hclosed : ∀ {x y : V}, x ∈ S → G.Adj x y → (c s(x, y) = α ∨ c s(x, y) = β) → y ∈ S) :
    IsProperSym2Coloring G (kempeSwap c α β S) := by
  intro x y z hxy hxz hne
  by_cases hx : x ∈ S
  · rw [kempeSwap_apply_of_mem hclosed hxy hx,
        kempeSwap_apply_of_mem hclosed hxz hx]
    exact (Equiv.swap α β).injective.ne (hc hxy hxz hne)
  · rw [kempeSwap_apply_of_notMem hxy hx, kempeSwap_apply_of_notMem hxz hx]
    exact hc hxy hxz hne

private theorem missingColors_kempeSwap {V K : Type*} [Fintype K] [DecidableEq K]
    {G : _root_.SimpleGraph V} {c : Sym2 V → K}
    {α β : K} {S : Set V}
    (hclosed : ∀ {x y : V}, x ∈ S → G.Adj x y → (c s(x, y) = α ∨ c s(x, y) = β) → y ∈ S)
    {x : V} (hx : x ∈ S) :
    missingColors G (kempeSwap c α β S) x =
      (missingColors G c x).map (Equiv.swap α β).toEmbedding := by
  classical
  apply Finset.ext
  intro i
  rw [Finset.mem_map_equiv, Equiv.symm_swap]
  simp only [mem_missingColors_iff]
  constructor
  · intro h y hy
    have hswap : kempeSwap c α β S s(x, y) = Equiv.swap α β (c s(x, y)) :=
      kempeSwap_apply_of_mem hclosed hy hx
    have hne : kempeSwap c α β S s(x, y) ≠ i := h y hy
    rw [hswap] at hne
    intro hcon
    apply hne
    rw [hcon, Equiv.swap_apply_self]
  · intro h y hy
    have hswap : kempeSwap c α β S s(x, y) = Equiv.swap α β (c s(x, y)) :=
      kempeSwap_apply_of_mem hclosed hy hx
    rw [hswap]
    intro hcon
    exact (h y hy) (by have h2 := congrArg (Equiv.swap α β) hcon; rwa [Equiv.swap_apply_self] at h2)

private theorem missingColors_kempeSwap_of_notMem {V K : Type*} [Fintype K] [DecidableEq K]
    {G : _root_.SimpleGraph V} {c : Sym2 V → K}
    {α β : K} {S : Set V}
    (_hclosed : ∀ {x y : V}, x ∈ S → G.Adj x y → (c s(x, y) = α ∨ c s(x, y) = β) → y ∈ S)
    {x : V} (hx : x ∉ S) :
    missingColors G (kempeSwap c α β S) x = missingColors G c x := by
  classical
  apply Finset.ext
  intro i
  simp only [mem_missingColors_iff]
  constructor <;> intro h y hy
  · have hswap := kempeSwap_apply_of_notMem (c := c) (α := α) (β := β) (S := S) hy hx
    rw [← hswap]
    exact h y hy
  · have hswap := kempeSwap_apply_of_notMem (c := c) (α := α) (β := β) (S := S) hy hx
    rw [hswap]
    exact h y hy

/-- Missing colors plus degree equals number of colors. -/
private theorem card_missingColors_add_degree {V K : Type*} [Fintype K] [DecidableEq K]
    [Fintype V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {c : Sym2 V → K} (hc : IsProperSym2Coloring G c) (u : V) :
    (missingColors G c u).card + G.degree u = Fintype.card K := by
  classical
  have hcompl : (missingColors G c u).card +
      (Finset.univ.filter (fun i => ∃ (y : V), ∃ (_ : G.Adj u y), c s(u, y) = i)).card =
      Fintype.card K := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset K))
      (fun i => ∀ (y : V), G.Adj u y → c s(u, y) ≠ i)
    rw [Finset.card_univ] at h
    have heq : (Finset.univ.filter (fun i => ¬∀ (y : V), G.Adj u y → c s(u, y) ≠ i)) =
        (Finset.univ.filter (fun i => ∃ (y : V), ∃ (_ : G.Adj u y), c s(u, y) = i)) := by
      apply Finset.filter_congr
      intro i _
      simp only [not_forall, not_not]
    rw [heq] at h
    have hmiss : Finset.filter (fun i => ∀ (y : V), G.Adj u y → c s(u, y) ≠ i) Finset.univ =
        missingColors G c u := by
      simp [missingColors]
    rw [hmiss] at h
    omega
  suffices himg : (Finset.univ.filter
      (fun i => ∃ (y : V), ∃ (_ : G.Adj u y), c s(u, y) = i)).card = G.degree u by omega
  have hinj : Set.InjOn (fun y => c s(u, y)) (↑(G.neighborFinset u) : Set V) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    have ha' : G.Adj u a := (SimpleGraph.mem_neighborFinset G u a).mp ha
    have hb' : G.Adj u b := (SimpleGraph.mem_neighborFinset G u b).mp hb
    by_contra hne
    exact hc ha' hb' hne hab
  have hcards : ((G.neighborFinset u).image (fun y => c s(u, y))).card = G.degree u := by
    rw [Finset.card_image_of_injOn hinj]
    exact SimpleGraph.card_neighborFinset_eq_degree G u
  have hsub : (G.neighborFinset u).image (fun y => c s(u, y)) =
      (Finset.univ.filter (fun i => ∃ (y : V), ∃ (_ : G.Adj u y), c s(u, y) = i)) := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (SimpleGraph.mem_neighborFinset G u y).mp hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (SimpleGraph.mem_neighborFinset G u y).mpr hy, rfl⟩
  rw [← hsub, hcards]

private theorem degree_deleteIncidenceSet_add_one {V : Type*} [Fintype V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {v u : V} [DecidableRel (G.deleteIncidenceSet v).Adj] (h : G.Adj v u) :
    (G.deleteIncidenceSet v).degree u + 1 = G.degree u := by
  classical
  have hne : u ≠ v := Ne.symm h.ne
  have herase : (G.deleteIncidenceSet v).neighborFinset u = (G.neighborFinset u).erase v := by
    apply Finset.ext
    intro w
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteIncidenceSet_adj,
      Finset.mem_erase]
    constructor
    · rintro ⟨hadj, _, hne2⟩
      exact ⟨hne2, hadj⟩
    · rintro ⟨hne2, hadj⟩
      exact ⟨hadj, hne, hne2⟩
  have hmem : v ∈ G.neighborFinset u :=
    (SimpleGraph.mem_neighborFinset G u v).mpr h.symm
  have hcard : ((G.neighborFinset u).erase v).card + 1 = (G.neighborFinset u).card :=
    Finset.card_erase_add_one hmem
  have d1 := SimpleGraph.card_neighborFinset_eq_degree (G.deleteIncidenceSet v) u
  have d2 := SimpleGraph.card_neighborFinset_eq_degree G u
  rw [herase] at d1
  omega

private theorem degree_add_one_le_of_adj_of_not_adj {V : Type*} [Fintype V]
    {G H : _root_.SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : H ≤ G) {u y : V} (hadj : G.Adj u y) (hnot : ¬ H.Adj u y) :
    H.degree u + 1 ≤ G.degree u := by
  classical
  have hsub : H.neighborFinset u ⊆ G.neighborFinset u := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact hle hw
  have hss : H.neighborFinset u ⊂ G.neighborFinset u := by
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨y, ?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset]
      exact hadj
    · intro hy
      rw [SimpleGraph.mem_neighborFinset] at hy
      exact hnot hy
  have hlt := Finset.card_lt_card hss
  have d1 := SimpleGraph.card_neighborFinset_eq_degree H u
  have d2 := SimpleGraph.card_neighborFinset_eq_degree G u
  omega

private theorem card_filter_degree_le_one_le_two_of_connected
    {W : Type*} [Fintype W]
    {Γ : _root_.SimpleGraph W} [DecidableRel Γ.Adj]
    (hconn : Γ.Connected) (hdeg : ∀ x, Γ.degree x ≤ 2) :
    (Finset.univ.filter (fun x => Γ.degree x ≤ 1)).card ≤ 2 := by
  classical
  have hconn' : Fintype.card W ≤ Γ.edgeFinset.card + 1 := by
    have h := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card] at h
    have hedge : Nat.card (↑Γ.edgeSet) = Γ.edgeFinset.card := by
      rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
    omega
  have hhand : ∑ x : W, Γ.degree x = 2 * Γ.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges Γ
  have hpt : ∀ x : W, Γ.degree x + (if Γ.degree x ≤ 1 then 1 else 0) ≤ 2 := by
    intro x
    by_cases hx : Γ.degree x ≤ 1
    · rw [ite_eq_left hx]
      omega
    · rw [ite_eq_right hx]
      exact hdeg x
  have hsum : ∑ x : W, (Γ.degree x + (if Γ.degree x ≤ 1 then 1 else 0)) ≤ ∑ _x : W, 2 :=
    Finset.sum_le_sum (fun x _ => hpt x)
  rw [Finset.sum_add_distrib, hhand] at hsum
  have hboole : (∑ x : W, (if Γ.degree x ≤ 1 then 1 else 0)) =
      (Finset.univ.filter (fun x => Γ.degree x ≤ 1)).card := by
    simp
  have hconst : (∑ _x : W, 2) = 2 * Fintype.card W := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  rw [hboole, hconst] at hsum
  omega

/-- In a graph of maximum degree 2, a set of pairwise reachable vertices
of degree at most 1 has at most 2 elements. -/
private theorem card_le_two_of_forall_reachable_of_degree_le_one
    {V : Type*} [Fintype V]
    {Γ : _root_.SimpleGraph V} [DecidableRel Γ.Adj]
    (hdeg : ∀ x, Γ.degree x ≤ 2)
    {A : Finset V} (hA1 : ∀ a ∈ A, Γ.degree a ≤ 1)
    (hAreach : ∀ a ∈ A, ∀ b ∈ A, Γ.Reachable a b) :
    A.card ≤ 2 := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨a0, ha0⟩ := hA
    set C : Γ.ConnectedComponent := Γ.connectedComponentMk a0 with hC
    have hconn : (Γ.induce C.supp).Connected :=
      SimpleGraph.ConnectedComponent.connected_toSimpleGraph C
    have hdegC : ∀ x : ↥(C.supp), (Γ.induce C.supp).degree x ≤ 2 := by
      intro x
      have hsub : Γ.neighborSet x.val ⊆ C.supp := by
        intro w hw
        rw [SimpleGraph.mem_neighborSet] at hw
        exact SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp C x.property hw
      have heq := SimpleGraph.degree_induce_of_neighborSet_subset (G := Γ) hsub
      rw [heq]
      exact hdeg x.val
    have hlow := card_filter_degree_le_one_le_two_of_connected hconn hdegC
    have hAsupp : ∀ a ∈ A, a ∈ C.supp := by
      intro a haA
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff, hC]
      exact (SimpleGraph.ConnectedComponent.sound (hAreach a0 ha0 a haA)).symm
    let T := Finset.univ.filter (fun x : ↥(C.supp) => (Γ.induce C.supp).degree x ≤ 1)
    let e : ↥(C.supp) ↪ V := Function.Embedding.subtype _
    have hsub : A ⊆ T.map e := by
      intro a haA
      have hmem : (⟨a, hAsupp a haA⟩ : ↥(C.supp)) ∈ T := by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        have hsub2 : Γ.neighborSet a ⊆ C.supp := by
          intro w hw
          rw [SimpleGraph.mem_neighborSet] at hw
          exact SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp C
            (hAsupp a haA) hw
        have heq := SimpleGraph.degree_induce_of_neighborSet_subset (G := Γ)
          (v := (⟨a, hAsupp a haA⟩ : ↥(C.supp))) hsub2
        rw [heq]
        exact hA1 a haA
      exact Finset.mem_map.mpr ⟨⟨a, hAsupp a haA⟩, hmem, rfl⟩
    calc A.card ≤ (T.map e).card := Finset.card_le_card hsub
      _ = T.card := Finset.card_map e
      _ ≤ 2 := hlow
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA, Finset.card_empty]
    exact Nat.zero_le 2

/-- In a graph of maximum degree 2, an odd set of vertices of degree at most 1
contains a vertex reachable from no other element of the set. -/
private theorem exists_mem_forall_reachable_eq_of_odd_card
    {V : Type*} [Fintype V]
    {Γ : _root_.SimpleGraph V} [DecidableRel Γ.Adj]
    (hdeg : ∀ x, Γ.degree x ≤ 2)
    {A : Finset V} (hA1 : ∀ a ∈ A, Γ.degree a ≤ 1)
    (hodd : Odd A.card) :
    ∃ w ∈ A, ∀ a ∈ A, Γ.Reachable w a → a = w := by
  classical
  have hcard := Finset.card_eq_sum_card_image Γ.connectedComponentMk A
  have hfib2 : ∀ c ∈ A.image Γ.connectedComponentMk,
      (A.filter (fun a => Γ.connectedComponentMk a = c)).card ≤ 2 := by
    intro c hc
    refine card_le_two_of_forall_reachable_of_degree_le_one hdeg ?_ ?_
    · intro a ha
      rw [Finset.mem_filter] at ha
      exact hA1 a ha.1
    · intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      apply SimpleGraph.ConnectedComponent.exact
      exact ha.2.trans hb.2.symm
  have hfibpos : ∀ c ∈ A.image Γ.connectedComponentMk,
      0 < (A.filter (fun a => Γ.connectedComponentMk a = c)).card := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨a, haA, rfl⟩ := hc
    apply Finset.card_pos.mpr
    exact ⟨a, Finset.mem_filter.mpr ⟨haA, rfl⟩⟩
  by_cases hyes : ∃ c ∈ A.image Γ.connectedComponentMk,
      (A.filter (fun a => Γ.connectedComponentMk a = c)).card = 1
  · obtain ⟨c, _, hc1⟩ := hyes
    rw [Finset.card_eq_one] at hc1
    obtain ⟨w, hw⟩ := hc1
    have hwmem : w ∈ A.filter (fun a => Γ.connectedComponentMk a = c) := by
      rw [hw]
      exact Finset.mem_singleton_self w
    rw [Finset.mem_filter] at hwmem
    refine ⟨w, hwmem.1, fun a haA hreach => ?_⟩
    have hfab : Γ.connectedComponentMk a = Γ.connectedComponentMk w :=
      (SimpleGraph.ConnectedComponent.sound hreach).symm
    have hafib : a ∈ A.filter (fun a => Γ.connectedComponentMk a = c) := by
      rw [Finset.mem_filter]
      exact ⟨haA, by rw [hfab, hwmem.2]⟩
    rw [hw, Finset.mem_singleton] at hafib
    exact hafib
  · push Not at hyes
    have h2 : ∀ c ∈ A.image Γ.connectedComponentMk,
        (A.filter (fun a => Γ.connectedComponentMk a = c)).card = 2 := by
      intro c hc
      have hle := hfib2 c hc
      have hne1 := hyes c hc
      have hpos := hfibpos c hc
      omega
    have hsum : ∑ c ∈ A.image Γ.connectedComponentMk,
        (A.filter (fun a => Γ.connectedComponentMk a = c)).card =
        2 * (A.image Γ.connectedComponentMk).card := by
      have hcongr : ∑ c ∈ A.image Γ.connectedComponentMk,
          (A.filter (fun a => Γ.connectedComponentMk a = c)).card =
          ∑ _c ∈ A.image Γ.connectedComponentMk, 2 :=
        Finset.sum_congr rfl h2
      rw [hcongr, Finset.sum_const, smul_eq_mul, mul_comm]
    have heven : Even A.card := ⟨(A.image Γ.connectedComponentMk).card, by omega⟩
    exact ((Nat.not_even_iff_odd.mpr hodd) heven).elim

private theorem exists_singleton_or_odd_and_empty
    {V K : Type*} [Fintype K] [DecidableEq K]
    {N : Finset V} {D : V → Finset K}
    (hsum : (∑ u ∈ N, (D u).card) + 1 = 2 * N.card)
    (hle : N.card ≤ Fintype.card K) :
    (∃ γ w, N.filter (fun u => γ ∈ D u) = {w}) ∨
    (∃ α β, α ≠ β ∧ Odd (N.filter (fun u => α ∈ D u)).card ∧
      N.filter (fun u => β ∈ D u) = ∅) := by
  classical
  have habove : ∀ u : V,
      Finset.bipartiteAbove (fun (u : V) (γ : K) => γ ∈ D u) Finset.univ u = D u := by
    intro u
    apply Finset.ext
    intro γ
    simp [Finset.bipartiteAbove]
  have hbelow : ∀ γ : K, Finset.bipartiteBelow (fun (u : V) (γ : K) => γ ∈ D u) N γ =
      N.filter (fun u => γ ∈ D u) := by
    intro γ
    apply Finset.ext
    intro u
    simp [Finset.bipartiteBelow]
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun (u : V) (γ : K) => γ ∈ D u) (s := N) (t := Finset.univ)
  simp only [habove, hbelow] at h
  -- h : ∑ u ∈ N, (D u).card = ∑ γ ∈ univ, card X_γ
  have hdouble : ∑ γ ∈ (Finset.univ : Finset K), (N.filter (fun u => γ ∈ D u)).card =
      ∑ u ∈ N, (D u).card := h.symm
  have htotal : ∑ γ ∈ (Finset.univ : Finset K), (N.filter (fun u => γ ∈ D u)).card + 1 =
      2 * N.card := by rw [hdouble]; exact hsum
  have hNpos : 0 < N.card := by omega
  obtain ⟨n, hn⟩ : ∃ n, N.card = n + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  have hSval : ∑ γ ∈ (Finset.univ : Finset K), (N.filter (fun u => γ ∈ D u)).card = 2 * n + 1 := by
    omega
  have hodd_total : Odd (∑ γ ∈ (Finset.univ : Finset K), (N.filter (fun u => γ ∈ D u)).card) := by
    rw [hSval]
    exact ⟨n, rfl⟩
  rw [Finset.odd_sum_iff_odd_card_odd] at hodd_total
  -- hodd_total : Odd (filter univ (fun γ => Odd (card X_γ))).card
  have hcard_ne :
      (Finset.univ.filter (fun γ => Odd (N.filter (fun u => γ ∈ D u)).card)).card ≠ 0 := by
    intro h0
    rw [h0] at hodd_total
    exact Nat.not_odd_zero hodd_total
  have hne :
      (Finset.univ.filter (fun γ => Odd (N.filter (fun u => γ ∈ D u)).card)).Nonempty :=
    Finset.card_pos.mp (Nat.pos_of_ne_zero hcard_ne)
  obtain ⟨α, hα⟩ := hne
  rw [Finset.mem_filter] at hα
  -- hα.2 : Odd (card X_α)
  by_cases hsingle : ∃ γ, (N.filter (fun u => γ ∈ D u)).card = 1
  · obtain ⟨γ, hγ⟩ := hsingle
    rw [Finset.card_eq_one] at hγ
    obtain ⟨w, hw⟩ := hγ
    exact Or.inl ⟨γ, w, hw⟩
  · -- every card ≠ 1; X_α card is odd so ≠ 0; show some X_β empty
    push Not at hsingle
    have hαcard : (N.filter (fun u => α ∈ D u)).card ≠ 0 := by
      intro h0
      rw [h0] at hα
      exact Nat.not_odd_zero hα.2
    by_cases hempty : ∃ β, N.filter (fun u => β ∈ D u) = ∅
    · obtain ⟨β, hβ⟩ := hempty
      have hne' : α ≠ β := by
        intro heq
        subst heq
        exact hαcard (by rw [hβ, Finset.card_empty])
      exact Or.inr ⟨α, β, hne', hα.2, hβ⟩
    · push Not at hempty
      -- every X_γ nonempty, and card ≠ 1, so card ≥ 2; sum ≥ 2 * card K ≥ 2 * card N
      exfalso
      have hge : ∀ γ ∈ (Finset.univ : Finset K), 2 ≤ (N.filter (fun u => γ ∈ D u)).card := by
        intro γ _
        have hne' : (N.filter (fun u => γ ∈ D u)).card ≠ 0 := by
          intro h0
          exact (hempty γ).ne_empty (Finset.card_eq_zero.mp h0)
        have h1 : (N.filter (fun u => γ ∈ D u)).card ≠ 1 := hsingle γ
        omega
      have hbound := Finset.card_nsmul_le_sum (Finset.univ : Finset K)
        (fun γ => (N.filter (fun u => γ ∈ D u)).card) 2 hge
      rw [Finset.card_univ, smul_eq_mul] at hbound
      omega

/-- The subgraph of `G` formed by edges colored `α` or `β`. -/
private def kempeGraph {V K : Type*} [DecidableEq K]
    (G : _root_.SimpleGraph V) (c : Sym2 V → K) (α β : K) : _root_.SimpleGraph V :=
  G.deleteEdges { e | c e ≠ α ∧ c e ≠ β }

private theorem kempeGraph_adj {V K : Type*} [DecidableEq K]
    {G : _root_.SimpleGraph V} {c : Sym2 V → K} {α β : K} {x y : V} :
    (kempeGraph G c α β).Adj x y ↔ G.Adj x y ∧ (c s(x, y) = α ∨ c s(x, y) = β) := by
  simp [kempeGraph, SimpleGraph.deleteEdges_adj]
  tauto

private theorem kempeGraph_le {V K : Type*} [DecidableEq K]
    {G : _root_.SimpleGraph V} {c : Sym2 V → K} {α β : K} :
    kempeGraph G c α β ≤ G :=
  SimpleGraph.deleteEdges_le _

/-- Every vertex has Kempe-degree at most 2. -/
private theorem kempeGraph_degree_le_two {V K : Type*} [Fintype V] [DecidableEq K]
    {G : _root_.SimpleGraph V}
    {c : Sym2 V → K} (hc : IsProperSym2Coloring G c) (α β : K)
    [DecidableRel (kempeGraph G c α β).Adj] (x : V) :
    (kempeGraph G c α β).degree x ≤ 2 := by
  classical
  have hinj : Set.InjOn (fun y => c s(x, y))
      (↑((kempeGraph G c α β).neighborFinset x) : Set V) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    have haG : G.Adj x a := (kempeGraph_le (G := G) (c := c) (α := α) (β := β)
      ((SimpleGraph.mem_neighborFinset _ x a).mp ha))
    have hbG : G.Adj x b := (kempeGraph_le (G := G) (c := c) (α := α) (β := β)
      ((SimpleGraph.mem_neighborFinset _ x b).mp hb))
    by_contra hne
    exact hc haG hbG hne hab
  have hmaps : ((kempeGraph G c α β).neighborFinset x).image (fun y => c s(x, y)) ⊆ {α, β} := by
    intro i hi
    simp only [Finset.mem_image] at hi
    obtain ⟨y, hy, rfl⟩ := hi
    have hadj := (SimpleGraph.mem_neighborFinset _ x y).mp hy
    have hcol : c s(x, y) = α ∨ c s(x, y) = β := (kempeGraph_adj.mp hadj).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hcol
  calc (kempeGraph G c α β).degree x
      = (((kempeGraph G c α β).neighborFinset x).image (fun y => c s(x, y))).card := by
        rw [Finset.card_image_of_injOn hinj,
          SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ ({α, β} : Finset K).card := Finset.card_le_card hmaps
    _ ≤ 2 := Finset.card_le_two

/-- At a vertex missing `α`, Kempe-degree is at most 1. -/
private theorem kempeGraph_degree_le_one_of_mem_missingColors {V K : Type*} [Fintype V]
    [Fintype K] [DecidableEq K]
    {G : _root_.SimpleGraph V}
    {c : Sym2 V → K} (hc : IsProperSym2Coloring G c) {α β : K}
    [DecidableRel (kempeGraph G c α β).Adj] {x : V}
    (hx : α ∈ missingColors G c x) :
    (kempeGraph G c α β).degree x ≤ 1 := by
  classical
  rw [mem_missingColors_iff] at hx
  have hinj : Set.InjOn (fun y => c s(x, y))
      (↑((kempeGraph G c α β).neighborFinset x) : Set V) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    have haG : G.Adj x a := (kempeGraph_le (G := G) (c := c) (α := α) (β := β)
      ((SimpleGraph.mem_neighborFinset _ x a).mp ha))
    have hbG : G.Adj x b := (kempeGraph_le (G := G) (c := c) (α := α) (β := β)
      ((SimpleGraph.mem_neighborFinset _ x b).mp hb))
    by_contra hne
    exact hc haG hbG hne hab
  have hmaps : ((kempeGraph G c α β).neighborFinset x).image (fun y => c s(x, y)) ⊆ {β} := by
    intro i hi
    simp only [Finset.mem_image] at hi
    obtain ⟨y, hy, rfl⟩ := hi
    have hadj := (SimpleGraph.mem_neighborFinset _ x y).mp hy
    have hyG : G.Adj x y := (kempeGraph_adj.mp hadj).1
    have hcol : c s(x, y) = α ∨ c s(x, y) = β := (kempeGraph_adj.mp hadj).2
    rcases hcol with h | h
    · exact absurd h (hx y hyG)
    · exact Finset.mem_singleton.mpr h
  calc (kempeGraph G c α β).degree x
      = (((kempeGraph G c α β).neighborFinset x).image (fun y => c s(x, y))).card := by
        rw [Finset.card_image_of_injOn hinj,
          SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ ({β} : Finset K).card := Finset.card_le_card hmaps
    _ = 1 := Finset.card_singleton β

/-- Kempe step: from an odd `α`-set and an empty `β`-set, recolor to make
the `β`-set a singleton, preserving designated-set sizes. -/
private theorem exists_recoloring_singleton_of_odd_of_empty
    {V K : Type*} [Finite V] [Fintype K] [DecidableEq K]
    {G' : _root_.SimpleGraph V}
    {c : Sym2 V → K} (hc : IsProperSym2Coloring G' c)
    {N : Finset V} {D : V → Finset K}
    (hDsub : ∀ u ∈ N, D u ⊆ missingColors G' c u)
    {α β : K}
    (hodd : Odd (N.filter (fun u => α ∈ D u)).card)
    (hempty : N.filter (fun u => β ∈ D u) = ∅) :
    ∃ (c' : Sym2 V → K) (D' : V → Finset K) (w : V),
      IsProperSym2Coloring G' c' ∧
      (∀ u ∈ N, D' u ⊆ missingColors G' c' u ∧ (D' u).card = (D u).card) ∧
      N.filter (fun u => β ∈ D' u) = {w} := by
  classical
  have := Fintype.ofFinite V
  have hdeg2 : ∀ x, (kempeGraph G' c α β).degree x ≤ 2 :=
    fun x => kempeGraph_degree_le_two hc α β x
  have hdeg1 : ∀ a ∈ N.filter (fun u => α ∈ D u),
      (kempeGraph G' c α β).degree a ≤ 1 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    apply kempeGraph_degree_le_one_of_mem_missingColors hc
    exact hDsub a ha.1 ha.2
  obtain ⟨w, hwmem, huniq⟩ := exists_mem_forall_reachable_eq_of_odd_card
    (Γ := kempeGraph G' c α β) hdeg2 hdeg1 hodd
  rw [Finset.mem_filter] at hwmem
  set S : Set V := {y | (kempeGraph G' c α β).Reachable w y} with hS
  have hSmem : ∀ y : V, y ∈ S ↔ (kempeGraph G' c α β).Reachable w y :=
    fun y => Iff.rfl
  have hclosed : ∀ {x y : V}, x ∈ S → G'.Adj x y →
      (c s(x, y) = α ∨ c s(x, y) = β) → y ∈ S := by
    intro x y hx hadj hcol
    rw [hSmem] at hx ⊢
    have hkad : (kempeGraph G' c α β).Adj x y :=
      kempeGraph_adj.mpr ⟨hadj, hcol⟩
    exact hx.trans hkad.reachable
  set c' : Sym2 V → K := kempeSwap c α β S with hc'
  have hc'prop : IsProperSym2Coloring G' c' :=
    isProperSym2Coloring_kempeSwap hc hclosed
  set D' : V → Finset K := fun u =>
    if u ∈ S then (D u).map (Equiv.swap α β).toEmbedding else D u with hD'
  have hD' : ∀ u ∈ N,
      D' u ⊆ missingColors G' c' u ∧ (D' u).card = (D u).card := by
    intro u huN
    by_cases huS : u ∈ S
    · have hmiss : missingColors G' c' u =
          (missingColors G' c u).map (Equiv.swap α β).toEmbedding :=
        missingColors_kempeSwap hclosed huS
      have hmap : D' u = (D u).map (Equiv.swap α β).toEmbedding :=
        ite_eq_left huS
      rw [hmap, hmiss]
      exact ⟨Finset.map_subset_map.mpr (hDsub u huN), Finset.card_map _⟩
    · have hmiss : missingColors G' c' u = missingColors G' c u :=
        missingColors_kempeSwap_of_notMem hclosed huS
      have hDu : D' u = D u := ite_eq_right huS
      rw [hDu, hmiss]
      exact ⟨hDsub u huN, rfl⟩
  have hswapβ : Equiv.swap α β β = α := Equiv.swap_apply_right α β
  refine ⟨c', D', w, hc'prop, hD', ?_⟩
  rw [Finset.eq_singleton_iff_unique_mem]
  have hwS : w ∈ S :=
    (hSmem w).mpr (SimpleGraph.Reachable.refl w)
  have hmapw : D' w = (D w).map (Equiv.swap α β).toEmbedding :=
    ite_eq_left hwS
  constructor
  · rw [Finset.mem_filter]
    refine ⟨hwmem.1, ?_⟩
    rw [hmapw, Finset.mem_map_equiv, Equiv.symm_swap, hswapβ]
    exact hwmem.2
  · intro u hu
    rw [Finset.mem_filter] at hu
    by_cases huS : u ∈ S
    · have hmap : D' u = (D u).map (Equiv.swap α β).toEmbedding :=
        ite_eq_left huS
      rw [hmap, Finset.mem_map_equiv, Equiv.symm_swap, hswapβ] at hu
      have huX : u ∈ N.filter (fun u => α ∈ D u) :=
        Finset.mem_filter.mpr ⟨hu.1, hu.2⟩
      exact huniq u huX ((hSmem u).mp huS)
    · have hDu : D' u = D u := ite_eq_right huS
      rw [hDu] at hu
      have hmem : u ∈ N.filter (fun u => β ∈ D u) :=
        Finset.mem_filter.mpr ⟨hu.1, hu.2⟩
      rw [hempty] at hmem
      exact (Finset.notMem_empty u hmem).elim

/-- Gluing a color class back: if `H = G.deleteEdges M` is properly colored with
colors different from `γ`, and `M` is a matching, then coloring `M` with `γ`
gives a proper coloring of `G`. -/
private theorem isProperSym2Coloring_glue {V K : Type*}
    {G : _root_.SimpleGraph V} {M : Set (Sym2 V)} {γ : K}
    {ψ : Sym2 V → { x : K // x ≠ γ }}
    (hψ : IsProperSym2Coloring (G.deleteEdges M) ψ)
    (hmatch : ∀ {x y z : V}, G.Adj x y → G.Adj x z → y ≠ z →
      s(x, y) ∈ M → s(x, z) ∈ M → False) :
    open Classical in
    IsProperSym2Coloring G (fun e => if e ∈ M then γ else (ψ e).val) := by
  classical
  intro x y z hxy hxz hne
  by_cases h1 : s(x, y) ∈ M <;> by_cases h2 : s(x, z) ∈ M
  · simp only [h1, h2]
    exact (hmatch hxy hxz hne h1 h2).elim
  · simp only [h1, h2]
    exact Ne.symm (ψ s(x, z)).property
  · simp only [h1, h2]
    exact (ψ s(x, y)).property
  · simp only [h1, h2]
    have g1 : (G.deleteEdges M).Adj x y :=
      SimpleGraph.deleteEdges_adj.mpr ⟨hxy, h1⟩
    have g2 : (G.deleteEdges M).Adj x z :=
      SimpleGraph.deleteEdges_adj.mpr ⟨hxz, h2⟩
    have h := hψ g1 g2 hne
    exact fun heq => h (Subtype.val_injective heq)

/-- The deleted edges in the EFK reduction form a matching inside `G`. -/
private theorem reduction_isMatching
    {V K : Type*} [Fintype V] [Fintype K] [DecidableEq K]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {v w : V} {c' : Sym2 V → K} {D' : V → Finset K} {γ : K}
    (hc' : IsProperSym2Coloring (G.deleteIncidenceSet v) c')
    (hDsub : ∀ u ∈ G.neighborFinset v,
      D' u ⊆ missingColors (G.deleteIncidenceSet v) c' u)
    (hsingle : (G.neighborFinset v).filter (fun u => γ ∈ D' u) = {w})
    {M : Set (Sym2 V)}
    (hM : ∀ e : Sym2 V, e ∈ M ↔
      ((e ∈ (G.deleteIncidenceSet v).edgeSet ∧ c' e = γ) ∨ e = s(v, w))) :
    ∀ {x y z : V}, G.Adj x y → G.Adj x z → y ≠ z →
      s(x, y) ∈ M → s(x, z) ∈ M → False := by
  classical
  intro x y z hxy hxz hne hm1 hm2
  rw [hM] at hm1 hm2
  have hwN : w ∈ G.neighborFinset v ∧ γ ∈ D' w := by
    have hmem : w ∈ (G.neighborFinset v).filter (fun u => γ ∈ D' u) := by
      rw [hsingle]
      exact Finset.mem_singleton_self w
    rw [Finset.mem_filter] at hmem
    exact hmem
  have hmiss : ∀ t : V, (G.deleteIncidenceSet v).Adj w t → c' s(w, t) ≠ γ := by
    have hsub := hDsub w hwN.1 hwN.2
    rw [mem_missingColors_iff] at hsub
    exact hsub
  rcases hm1 with ⟨hm1e, hm1c⟩ | hm1e <;> rcases hm2 with ⟨hm2e, hm2c⟩ | hm2e
  · have g1 : (G.deleteIncidenceSet v).Adj x y :=
      (G.deleteIncidenceSet v).mem_edgeSet.mp hm1e
    have g2 : (G.deleteIncidenceSet v).Adj x z :=
      (G.deleteIncidenceSet v).mem_edgeSet.mp hm2e
    exact hc' g1 g2 hne (hm1c.trans hm2c.symm)
  · have g1 : (G.deleteIncidenceSet v).Adj x y :=
      (G.deleteIncidenceSet v).mem_edgeSet.mp hm1e
    rw [SimpleGraph.deleteIncidenceSet_adj] at g1
    rw [Sym2.eq_iff] at hm2e
    rcases hm2e with ⟨hxv, -⟩ | ⟨hxw, -⟩
    · exact g1.2.1 hxv
    · rw [hxw] at hm1c g1
      have g1' : (G.deleteIncidenceSet v).Adj w y :=
        SimpleGraph.deleteIncidenceSet_adj.mpr ⟨g1.1, g1.2.1, g1.2.2⟩
      exact hmiss y g1' hm1c
  · have g2 : (G.deleteIncidenceSet v).Adj x z :=
      (G.deleteIncidenceSet v).mem_edgeSet.mp hm2e
    rw [SimpleGraph.deleteIncidenceSet_adj] at g2
    rw [Sym2.eq_iff] at hm1e
    rcases hm1e with ⟨hxv, -⟩ | ⟨hxw, -⟩
    · exact g2.2.1 hxv
    · rw [hxw] at hm2c g2
      have g2' : (G.deleteIncidenceSet v).Adj w z :=
        SimpleGraph.deleteIncidenceSet_adj.mpr ⟨g2.1, g2.2.1, g2.2.2⟩
      exact hmiss z g2' hm2c
  · have heq : s(x, y) = s(x, z) := hm1e.trans hm2e.symm
    have hyz : y = z := Sym2.congr_right.mp heq
    exact hne hyz

/-- The reduced graph minus the edges at `v` inherits a coloring avoiding `γ`. -/
private theorem reduction_coloring
    {V K : Type*}
    {G : _root_.SimpleGraph V}
    {v w : V} {c' : Sym2 V → K} {γ : K}
    (hc' : IsProperSym2Coloring (G.deleteIncidenceSet v) c')
    {M : Set (Sym2 V)}
    (hM : ∀ e : Sym2 V, e ∈ M ↔
      ((e ∈ (G.deleteIncidenceSet v).edgeSet ∧ c' e = γ) ∨ e = s(v, w)))
    {δ : K} (hδ : δ ≠ γ) :
    ∃ ψ : Sym2 V → { x : K // x ≠ γ },
      IsProperSym2Coloring ((G.deleteEdges M).deleteIncidenceSet v) ψ := by
  classical
  set ψ : Sym2 V → { x : K // x ≠ γ } :=
    fun e => if h : c' e = γ then ⟨δ, hδ⟩ else ⟨c' e, h⟩ with hψ
  refine ⟨ψ, fun {x y z} h1 h2 hne => ?_⟩
  rw [SimpleGraph.deleteIncidenceSet_adj] at h1 h2
  rw [SimpleGraph.deleteEdges_adj] at h1 h2
  have g1 : (G.deleteIncidenceSet v).Adj x y :=
    SimpleGraph.deleteIncidenceSet_adj.mpr ⟨h1.1.1, h1.2.1, h1.2.2⟩
  have g2 : (G.deleteIncidenceSet v).Adj x z :=
    SimpleGraph.deleteIncidenceSet_adj.mpr ⟨h2.1.1, h2.2.1, h2.2.2⟩
  have hc1 : c' s(x, y) ≠ γ := by
    intro hcon
    have hmem : s(x, y) ∈ (G.deleteIncidenceSet v).edgeSet :=
      (G.deleteIncidenceSet v).mem_edgeSet.mpr g1
    have hnot := h1.1.2
    rw [hM] at hnot
    exact hnot (Or.inl ⟨hmem, hcon⟩)
  have hc2 : c' s(x, z) ≠ γ := by
    intro hcon
    have hmem : s(x, z) ∈ (G.deleteIncidenceSet v).edgeSet :=
      (G.deleteIncidenceSet v).mem_edgeSet.mpr g2
    have hnot := h2.1.2
    rw [hM] at hnot
    exact hnot (Or.inl ⟨hmem, hcon⟩)
  have hψ1 : ψ s(x, y) = ⟨c' s(x, y), hc1⟩ := dite_eq_right hc1
  have hψ2 : ψ s(x, z) = ⟨c' s(x, z), hc2⟩ := dite_eq_right hc2
  have hne' := hc' g1 g2 hne
  rw [hψ1, hψ2]
  exact fun heq => hne' (congrArg Subtype.val heq)

/-- In the EFK reduced graph, the degree of `v` drops by exactly one. -/
private theorem reduction_degree_v
    {V K : Type*} [Fintype V] [DecidableEq K]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {v w : V} {c' : Sym2 V → K} {D' : V → Finset K} {γ : K}
    (hsingle : (G.neighborFinset v).filter (fun u => γ ∈ D' u) = {w})
    {M : Set (Sym2 V)}
    (hM : ∀ e : Sym2 V, e ∈ M ↔
      ((e ∈ (G.deleteIncidenceSet v).edgeSet ∧ c' e = γ) ∨ e = s(v, w)))
    [DecidableRel (G.deleteEdges M).Adj] :
    (G.deleteEdges M).degree v + 1 = G.degree v := by
  classical
  have hwN : w ∈ G.neighborFinset v := by
    have hmem : w ∈ (G.neighborFinset v).filter (fun u => γ ∈ D' u) := by
      rw [hsingle]
      exact Finset.mem_singleton_self w
    rw [Finset.mem_filter] at hmem
    exact hmem.1
  have herase : (G.deleteEdges M).neighborFinset v = (G.neighborFinset v).erase w := by
    apply Finset.ext
    intro u
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj,
      Finset.mem_erase]
    constructor
    · rintro ⟨hadjG, hnotM⟩
      refine ⟨?_, hadjG⟩
      intro hcon
      subst hcon
      exact hnotM ((hM _).mpr (Or.inr rfl))
    · rintro ⟨hne, hadjG⟩
      refine ⟨hadjG, ?_⟩
      intro hmem
      rw [hM] at hmem
      rcases hmem with ⟨hmeme, -⟩ | hmeq
      · have g : (G.deleteIncidenceSet v).Adj v u :=
          (G.deleteIncidenceSet v).mem_edgeSet.mp hmeme
        rw [SimpleGraph.deleteIncidenceSet_adj] at g
        exact g.2.1 rfl
      · have huw : u = w := Sym2.congr_right.mp hmeq
        exact hne huw
  have hcard : ((G.neighborFinset v).erase w).card + 1 =
      (G.neighborFinset v).card :=
    Finset.card_erase_add_one hwN
  have d1 := SimpleGraph.card_neighborFinset_eq_degree (G.deleteEdges M) v
  have d2 := SimpleGraph.card_neighborFinset_eq_degree G v
  rw [herase] at d1
  omega

/-- In the EFK reduced graph, neighbors of `v` satisfy the degree-plus-designated
bound. -/
private theorem reduction_degree_le
    {V K : Type*} [Fintype V] [Fintype K] [DecidableEq K]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {v w : V} {c' : Sym2 V → K} {D' : V → Finset K} {γ : K}
    (hc' : IsProperSym2Coloring (G.deleteIncidenceSet v) c')
    (hDsub : ∀ u ∈ G.neighborFinset v,
      D' u ⊆ missingColors (G.deleteIncidenceSet v) c' u)
    (hsingle : (G.neighborFinset v).filter (fun u => γ ∈ D' u) = {w})
    {M : Set (Sym2 V)}
    (hM : ∀ e : Sym2 V, e ∈ M ↔
      ((e ∈ (G.deleteIncidenceSet v).edgeSet ∧ c' e = γ) ∨ e = s(v, w)))
    [DecidableRel (G.deleteEdges M).Adj]
    {u : V} (hadj : (G.deleteEdges M).Adj v u) :
    (G.deleteEdges M).degree u + (D' u).card ≤ Fintype.card K := by
  classical
  rw [SimpleGraph.deleteEdges_adj] at hadj
  have hadjG : G.Adj v u := hadj.1
  have huN : u ∈ G.neighborFinset v :=
    (SimpleGraph.mem_neighborFinset G v u).mpr hadjG
  have huw : u ≠ w := by
    intro hcon
    subst hcon
    exact hadj.2 ((hM _).mpr (Or.inr rfl))
  have hN2a := card_missingColors_add_degree (G := G.deleteIncidenceSet v) hc' u
  have hN2b := degree_deleteIncidenceSet_add_one (h := hadjG)
  by_cases hγ : γ ∈ missingColors (G.deleteIncidenceSet v) c' u
  · have hγD : γ ∉ D' u := by
      intro hcon
      have hmem : u ∈ (G.neighborFinset v).filter (fun u => γ ∈ D' u) :=
        Finset.mem_filter.mpr ⟨huN, hcon⟩
      rw [hsingle, Finset.mem_singleton] at hmem
      exact huw hmem
    have hsub : insert γ (D' u) ⊆ missingColors (G.deleteIncidenceSet v) c' u :=
      Finset.insert_subset hγ (hDsub u huN)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hγD] at hcard
    have hle : (G.deleteEdges M).degree u ≤ G.degree u :=
      SimpleGraph.degree_le_of_le (SimpleGraph.deleteEdges_le M)
    omega
  · rw [mem_missingColors_iff] at hγ
    push Not at hγ
    obtain ⟨y, hyadj, hycol⟩ := hγ
    have hmemM : s(u, y) ∈ M := by
      rw [hM]
      refine Or.inl ⟨?_, hycol⟩
      exact (G.deleteIncidenceSet v).mem_edgeSet.mpr hyadj
    have hyG : G.Adj u y := SimpleGraph.deleteIncidenceSet_le G v hyadj
    have hnotH : ¬ (G.deleteEdges M).Adj u y := by
      rw [SimpleGraph.deleteEdges_adj]
      exact fun h => h.2 hmemM
    have hN2c := degree_add_one_le_of_adj_of_not_adj
      (SimpleGraph.deleteEdges_le M) hyG hnotH
    have hcard := Finset.card_le_card (hDsub u huN)
    omega

/-- EFK step: extend a coloring of `G` minus the edges at `v` to `G`,
using the main lemma at one fewer color. -/
private theorem efk_step
    {V : Type*} [Fintype V]
    {k' : ℕ} (hk' : 1 ≤ k')
    (ih : ∀ (K' : Type) [Fintype K'], Fintype.card K' = k' →
      ∀ {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (v : V),
        (∃ c : Sym2 V → K', IsProperSym2Coloring (G.deleteIncidenceSet v) c) →
        G.degree v ≤ k' →
        (∀ u, G.Adj v u → G.degree u ≤ k') →
        (∀ u1 u2, G.Adj v u1 → G.Adj v u2 → G.degree u1 = k' →
          G.degree u2 = k' → u1 = u2) →
        ∃ c0 : Sym2 V → K', IsProperSym2Coloring G c0)
    {K : Type} [Fintype K] (hK : Fintype.card K = k' + 1)
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (v : V)
    {c : Sym2 V → K} (hc : IsProperSym2Coloring (G.deleteIncidenceSet v) c)
    (hv : G.degree v ≤ k' + 1)
    (hdeg : ∀ u, G.Adj v u → G.degree u ≤ k' + 1)
    (huniq : ∀ u1 u2, G.Adj v u1 → G.Adj v u2 → G.degree u1 = k' + 1 →
      G.degree u2 = k' + 1 → u1 = u2) :
    ∃ c0 : Sym2 V → K, IsProperSym2Coloring G c0 := by
  classical
  have : DecidableEq K := fun a b => Classical.propDecidable (a = b)
  set N : Finset V := G.neighborFinset v with hN
  have hNcard : N.card = G.degree v :=
    SimpleGraph.card_neighborFinset_eq_degree G v
  by_cases hNempty : N.card = 0
  · have hadj : ∀ {a b : V}, G.Adj a b → (G.deleteIncidenceSet v).Adj a b := by
      intro a b hab
      rw [SimpleGraph.deleteIncidenceSet_adj]
      refine ⟨hab, ?_, ?_⟩
      · intro hcon
        rw [hcon] at hab
        have hmem : b ∈ N := (SimpleGraph.mem_neighborFinset G v b).mpr hab
        have hpos : 0 < N.card := Finset.card_pos.mpr ⟨b, hmem⟩
        omega
      · intro hcon
        rw [hcon] at hab
        have hmem : a ∈ N := (SimpleGraph.mem_neighborFinset G v a).mpr hab.symm
        have hpos : 0 < N.card := Finset.card_pos.mpr ⟨a, hmem⟩
        omega
    exact ⟨c, fun h1 h2 hne => hc (hadj h1) (hadj h2) hne⟩
  · have hNpos : 0 < N.card := Nat.pos_of_ne_zero hNempty
    have hex : ∃ s ∈ N, ∀ u ∈ N, u ≠ s → G.degree u ≤ k' := by
      by_cases htight : ∃ u ∈ N, G.degree u = k' + 1
      · obtain ⟨s, hsN, hsdeg⟩ := htight
        have hsadj : G.Adj v s := (SimpleGraph.mem_neighborFinset G v s).mp hsN
        exact ⟨s, hsN, fun u huN hne => by
          have hadj : G.Adj v u := (SimpleGraph.mem_neighborFinset G v u).mp huN
          have hle : G.degree u ≤ k' + 1 := hdeg u hadj
          have hne' : G.degree u ≠ k' + 1 :=
            fun heq => hne (huniq u s hadj hsadj heq hsdeg)
          omega⟩
      · obtain ⟨s, hsN⟩ := Finset.card_pos.mp hNpos
        exact ⟨s, hsN, fun u huN _ => by
          have hadj : G.Adj v u := (SimpleGraph.mem_neighborFinset G v u).mp huN
          have hle : G.degree u ≤ k' + 1 := hdeg u hadj
          have hne' : G.degree u ≠ k' + 1 := fun heq => htight ⟨u, huN, heq⟩
          omega⟩
    obtain ⟨s, hsN, hsmax⟩ := hex
    have hmiss : ∀ u ∈ N, (missingColors (G.deleteIncidenceSet v) c u).card +
        G.degree u = k' + 2 := by
      intro u huN
      have hadj : G.Adj v u := (SimpleGraph.mem_neighborFinset G v u).mp huN
      have hN2a := card_missingColors_add_degree (G := G.deleteIncidenceSet v) hc u
      have hN2b := degree_deleteIncidenceSet_add_one (h := hadj)
      omega
    have hsize : ∀ u ∈ N, (if u = s then 1 else 2) ≤
        (missingColors (G.deleteIncidenceSet v) c u).card := by
      intro u huN
      have hadj : G.Adj v u := (SimpleGraph.mem_neighborFinset G v u).mp huN
      have h := hmiss u huN
      by_cases hus : u = s
      · rw [ite_eq_left hus]
        have hle : G.degree u ≤ k' + 1 := hdeg u hadj
        omega
      · rw [ite_eq_right hus]
        have hle : G.degree u ≤ k' := hsmax u huN hus
        omega
    have hexD : ∀ u : V, ∃ E : Finset K,
        (u ∈ N → E ⊆ missingColors (G.deleteIncidenceSet v) c u) ∧
        (u ∈ N → E.card = (if u = s then 1 else 2)) := by
      intro u
      by_cases huN : u ∈ N
      · obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq (hsize u huN)
        exact ⟨E, fun _ => hEsub, fun _ => hEcard⟩
      · exact ⟨∅, fun h => absurd h huN, fun h => absurd h huN⟩
    choose D hDsub hDcard using hexD
    have hsum : (∑ u ∈ N, (D u).card) + 1 = 2 * N.card := by
      have hcard : ∀ u ∈ N, (D u).card = (if u = s then 1 else 2) :=
        fun u huN => hDcard u huN
      have hsplit : (D s).card + ∑ x ∈ N.erase s, (D x).card =
          ∑ x ∈ N, (D x).card :=
        Finset.add_sum_erase N (fun u => (D u).card) hsN
      have hserase : ∑ x ∈ N.erase s, (D x).card = 2 * (N.card - 1) := by
        have h2 : ∀ x ∈ N.erase s, (D x).card = 2 := by
          intro x hx
          rw [Finset.mem_erase] at hx
          rw [hcard x hx.2, ite_eq_right hx.1]
        have hcongr : ∑ x ∈ N.erase s, (D x).card = ∑ _x ∈ N.erase s, 2 :=
          Finset.sum_congr rfl h2
        rw [hcongr, Finset.sum_const, smul_eq_mul]
        have hce := Finset.card_erase_add_one hsN
        omega
      have hsD : (D s).card = 1 := by
        have h := hcard s hsN
        rw [ite_eq_left rfl] at h
        exact h
      omega
    have hNle : N.card ≤ Fintype.card K := by omega
    obtain ⟨c', D', γ, w, hc', hD'sub, hsingle⟩ :
        ∃ (c' : Sym2 V → K) (D' : V → Finset K) (γ : K) (w : V),
          IsProperSym2Coloring (G.deleteIncidenceSet v) c' ∧
          (∀ u ∈ N, D' u ⊆ missingColors (G.deleteIncidenceSet v) c' u ∧
            (D' u).card = (D u).card) ∧
          (N.filter (fun u => γ ∈ D' u) = {w}) := by
      rcases exists_singleton_or_odd_and_empty (N := N) (D := D) hsum hNle with
        hsing | hoddcase
      · obtain ⟨γ, w, hsing⟩ := hsing
        exact ⟨c, D, γ, w, hc, fun u huN => ⟨hDsub u huN, rfl⟩, hsing⟩
      · obtain ⟨α, β, _, hodd, hempty⟩ := hoddcase
        obtain ⟨c', D', w, hc'N9, hDN9, hsingN9⟩ :=
          exists_recoloring_singleton_of_odd_of_empty
            (G' := G.deleteIncidenceSet v) hc (fun u huN => hDsub u huN)
            hodd hempty
        exact ⟨c', D', β, w, hc'N9, hDN9, hsingN9⟩
    have hK2 : 1 < Fintype.card K := by omega
    obtain ⟨δ, hδ⟩ := Fintype.exists_ne_of_one_lt_card hK2 γ
    set M : Set (Sym2 V) := { e |
      ((e ∈ (G.deleteIncidenceSet v).edgeSet ∧ c' e = γ) ∨ e = s(v, w)) } with hMdef
    have hM : ∀ e : Sym2 V, e ∈ M ↔
        ((e ∈ (G.deleteIncidenceSet v).edgeSet ∧ c' e = γ) ∨ e = s(v, w)) :=
      fun e => Iff.rfl
    have hD'sub' : ∀ u ∈ G.neighborFinset v,
        D' u ⊆ missingColors (G.deleteIncidenceSet v) c' u :=
      fun u huN => (hD'sub u huN).1
    have hmatch : ∀ {x y z : V}, G.Adj x y → G.Adj x z → y ≠ z →
        s(x, y) ∈ M → s(x, z) ∈ M → False :=
      reduction_isMatching hc' hD'sub' hsingle hM
    obtain ⟨ψ, hψ⟩ := reduction_coloring hc' hM hδ
    have hDcard1 : ∀ u ∈ N, 1 ≤ (D' u).card := by
      intro u huN
      rw [(hD'sub u huN).2, hDcard u huN]
      split <;> omega
    have hDeq1 : ∀ u ∈ N, (D' u).card ≤ 1 → u = s := by
      intro u huN hle
      by_contra hcon
      rw [(hD'sub u huN).2, hDcard u huN, ite_eq_right hcon] at hle
      omega
    have hcompl : Fintype.card { x : K // x ≠ γ } =
        Fintype.card K - Fintype.card { x : K // x = γ } :=
      Fintype.card_subtype_compl _
    have h1 : Fintype.card { x : K // x = γ } = 1 :=
      @Fintype.card_unique _ ⟨⟨γ, rfl⟩, fun ⟨x, hx⟩ => Subtype.ext hx⟩ _
    have hcardK' : Fintype.card { x : K // x ≠ γ } = k' := by
      omega
    have hHdegv : (G.deleteEdges M).degree v ≤ k' := by
      have hdv := reduction_degree_v hsingle hM
      omega
    have hHdeg : ∀ u : V, (G.deleteEdges M).Adj v u →
        (G.deleteEdges M).degree u ≤ k' := by
      intro u hadjH
      have hadjG : G.Adj v u := SimpleGraph.deleteEdges_le M hadjH
      have huN : u ∈ N := (SimpleGraph.mem_neighborFinset G v u).mpr hadjG
      have hle : (G.deleteEdges M).degree u + (D' u).card ≤ Fintype.card K :=
        reduction_degree_le hc' hD'sub' hsingle hM hadjH
      have h1le := hDcard1 u huN
      omega
    have hHuniq : ∀ u1 u2 : V, (G.deleteEdges M).Adj v u1 →
        (G.deleteEdges M).Adj v u2 → (G.deleteEdges M).degree u1 = k' →
        (G.deleteEdges M).degree u2 = k' → u1 = u2 := by
      intro u1 u2 hadj1 hadj2 heq1 heq2
      have hu1N : u1 ∈ N :=
        (SimpleGraph.mem_neighborFinset G v u1).mpr
          (SimpleGraph.deleteEdges_le M hadj1)
      have hu2N : u2 ∈ N :=
        (SimpleGraph.mem_neighborFinset G v u2).mpr
          (SimpleGraph.deleteEdges_le M hadj2)
      have hle1 : (G.deleteEdges M).degree u1 + (D' u1).card ≤ Fintype.card K :=
        reduction_degree_le hc' hD'sub' hsingle hM hadj1
      have hle2 : (G.deleteEdges M).degree u2 + (D' u2).card ≤ Fintype.card K :=
        reduction_degree_le hc' hD'sub' hsingle hM hadj2
      have hs1 : u1 = s := hDeq1 u1 hu1N (by omega)
      have hs2 : u2 = s := hDeq1 u2 hu2N (by omega)
      rw [hs1, hs2]
    obtain ⟨ψH, hψH⟩ := ih { x : K // x ≠ γ } hcardK' v ⟨ψ, hψ⟩
      hHdegv hHdeg hHuniq
    have hglue : IsProperSym2Coloring G
        (fun e => @ite K (e ∈ M) (Classical.propDecidable (e ∈ M)) γ
          (ψH e).val) :=
      isProperSym2Coloring_glue hψH hmatch
    exact ⟨fun e => @ite K (e ∈ M) (Classical.propDecidable (e ∈ M)) γ
      (ψH e).val, hglue⟩

/-- EFK main lemma: induction on the number of colors. -/
private theorem efk_main {V : Type*} [Fintype V] (k : ℕ) :
    ∀ (K : Type) [Fintype K], Fintype.card K = k →
    ∀ {G : _root_.SimpleGraph V} [DecidableRel G.Adj] (v : V),
      (∃ c : Sym2 V → K, IsProperSym2Coloring (G.deleteIncidenceSet v) c) →
      G.degree v ≤ k →
      (∀ u, G.Adj v u → G.degree u ≤ k) →
      (∀ u1 u2, G.Adj v u1 → G.Adj v u2 → G.degree u1 = k → G.degree u2 = k →
        u1 = u2) →
      ∃ c0 : Sym2 V → K, IsProperSym2Coloring G c0 := by
  induction k with
  | zero =>
    intro K _ hK G _ v hex _ _ _
    rw [Fintype.card_eq_zero_iff] at hK
    obtain ⟨c, _⟩ := hex
    exact ⟨c, fun {x y z} _ _ _ => hK.elim (c s(x, y))⟩
  | succ k' ih =>
    intro K _ hK G _ v hex hv hdeg huniq
    by_cases hk' : k' = 0
    · subst hk'
      obtain ⟨c, hc⟩ := hex
      have hdeg2 : ∀ (a b₁ b₂ : V), G.Adj a b₁ → G.Adj a b₂ → b₁ ≠ b₂ →
          2 ≤ G.degree a := by
        classical
        intro a b₁ b₂ h1 h2 hne
        have hsub : ({b₁, b₂} : Finset V) ⊆ G.neighborFinset a := by
          intro w hw
          rw [Finset.mem_insert, Finset.mem_singleton] at hw
          rw [SimpleGraph.mem_neighborFinset]
          rcases hw with rfl | rfl
          · exact h1
          · exact h2
        have hle := Finset.card_le_card hsub
        rw [Finset.card_pair hne] at hle
        have hdeg := SimpleGraph.card_neighborFinset_eq_degree G a
        omega
      refine ⟨c, fun {x y z} h1 h2 hne => ?_⟩
      classical
      by_cases hxv : x = v
      · have h2 := hdeg2 v y z (hxv ▸ h1) (hxv ▸ h2) hne
        have hcontra : False := by omega
        exact hcontra.elim
      · by_cases hyv : y = v
        · have hxN : G.Adj v x := by rw [← hyv]; exact h1.symm
          have h2 := hdeg2 x y z h1 h2 hne
          have hle : G.degree x ≤ 0 + 1 := hdeg x hxN
          have hcontra : False := by omega
          exact hcontra.elim
        · by_cases hzv : z = v
          · have hxN : G.Adj v x := by rw [← hzv]; exact h2.symm
            have h2 := hdeg2 x y z h1 h2 hne
            have hle : G.degree x ≤ 0 + 1 := hdeg x hxN
            have hcontra : False := by omega
            exact hcontra.elim
          · have g1 : (G.deleteIncidenceSet v).Adj x y :=
              SimpleGraph.deleteIncidenceSet_adj.mpr ⟨h1, hxv, hyv⟩
            have g2 : (G.deleteIncidenceSet v).Adj x z :=
              SimpleGraph.deleteIncidenceSet_adj.mpr ⟨h2, hxv, hzv⟩
            exact hc g1 g2 hne
    · have hk'pos : 1 ≤ k' := Nat.pos_of_ne_zero hk'
      obtain ⟨c, hc⟩ := hex
      exact efk_step hk'pos ih hK v hc hv hdeg huniq

/-- Vizing's theorem for `Sym2` colorings: strong induction on the edge count. -/
private theorem exists_isProperSym2Coloring_of_degree_lt
    {V : Type*} [Fintype V] {K : Type} [Fintype K] [Nonempty K]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ u, G.degree u < Fintype.card K) :
    ∃ c : Sym2 V → K, IsProperSym2Coloring G c := by
  classical
  have : DecidableEq K := fun a b => Classical.propDecidable (a = b)
  have key : ∀ n : ℕ, ∀ (G : _root_.SimpleGraph V) [DecidableRel G.Adj],
      G.edgeFinset.card = n → (∀ u, G.degree u < Fintype.card K) →
      ∃ c : Sym2 V → K, IsProperSym2Coloring G c := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G _ hcard hdeg
      by_cases hzero : ∀ u, G.degree u = 0
      · refine ⟨fun _ => Classical.arbitrary K, fun {x y z} h1 _ _ => ?_⟩
        have hpos : 0 < G.degree x :=
          (SimpleGraph.degree_pos_iff_exists_adj G x).mpr ⟨y, h1⟩
        rw [hzero x] at hpos
        exact (lt_irrefl 0 hpos).elim
      · push Not at hzero
        obtain ⟨x, hx⟩ := hzero
        have hxpos : 0 < G.degree x := Nat.pos_of_ne_zero hx
        have hcard0 : (G.deleteIncidenceSet x).edgeFinset.card < n := by
          have hdel := SimpleGraph.card_edgeFinset_deleteIncidenceSet G x
          have h1 : (G.deleteIncidenceSet x).edgeFinset.card =
              G.edgeFinset.card - G.degree x := hdel
          have h2 : G.edgeFinset.card = n := hcard
          have hle : G.degree x ≤ G.edgeFinset.card :=
            SimpleGraph.degree_le_card_edgeFinset G x
          omega
        have hdeg0 : ∀ u, (G.deleteIncidenceSet x).degree u < Fintype.card K := by
          intro u
          have hle : (G.deleteIncidenceSet x).degree u ≤ G.degree u :=
            SimpleGraph.degree_le_of_le (SimpleGraph.deleteIncidenceSet_le G x)
          have hlt := hdeg u
          omega
        obtain ⟨c0, hc0⟩ := ih _ hcard0 (G.deleteIncidenceSet x) rfl hdeg0
        obtain ⟨c', hc'⟩ := efk_main _ K rfl x ⟨c0, hc0⟩
          (by have h := hdeg x; omega)
          (fun u _ => by have h := hdeg u; omega)
          (fun u1 u2 _ _ h1 _ => by
            have h := hdeg u1
            have hcontra : False := by omega
            exact hcontra.elim)
        exact ⟨c', hc'⟩
  exact key _ G rfl hdeg

/--
Every finite simple graph has edge chromatic number at most max degree plus one.
Source: V. G. Vizing, Diskret. Analiz 3 (1964), 25-30.

Proves `Wanted` entry `vizing`.
-/
theorem vizing :
    ∀ {V : Type*} (G : _root_.SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      ∃ C : G.EdgeLabeling (Fin (G.maxDegree + 1)), IsProperEdgeColoring C := by
  intro V G _ _
  have : Nonempty (Fin (G.maxDegree + 1)) := ⟨0⟩
  have hdeg : ∀ u, G.degree u < Fintype.card (Fin (G.maxDegree + 1)) := by
    intro u
    rw [Fintype.card_fin]
    have hle := SimpleGraph.degree_le_maxDegree G u
    omega
  obtain ⟨c, hc⟩ := exists_isProperSym2Coloring_of_degree_lt (K := Fin (G.maxDegree + 1)) hdeg
  exact ⟨fun e : G.edgeSet => c e.val,
    isProperEdgeColoring_of_isProperSym2Coloring hc⟩

end MathlibExt.Combinatorics.SimpleGraph.EdgeColoringWanted
end
