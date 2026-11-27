/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `2a4dcd009357b93b103d542487dfaa3fa6765d77`.

Original formalization by vonbers (@vonbo) and Avocado; ported with attribution.
Source: formal-math commit `bd2b030c7d44` (PR #6022).
-/

module

public import MathlibExt.Combinatorics.Digraph.PathCover
public import MathlibExt.Combinatorics.Matching.MaximumMatching
public import MathlibExt.Combinatorics.Digraph.FiniteDAG
public import MathlibExt.Combinatorics.Order.Dilworth
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Relation

@[expose] public section

section
namespace MathlibExt.Combinatorics.SimpleGraph.PathCoverGeneralWanted

open MathlibExt.Combinatorics.Digraph.PathCoverWanted (IsPath IsPathCover
  minPathCoverSize minPathCoverSize_le_card
  exists_isPathCover_card_eq_minPathCoverSize minPathCover_eq_maxAntichain
  transClosure transClosure_adj isTransitiveDAG_transClosure
  isAcyclic_transClosure)
open MathlibExt.Combinatorics.Order.DilworthWanted (maxAntichainSize
  minChainCoverSize dilworth_decomposition
  exists_isChainCoverFin_card_eq_minChainCoverSize)

/-!
# Minimum path cover of a general finite DAG

This file extends `MathlibExt.Combinatorics.Digraph.PathCover` (minimum path
covers of finite *transitive* DAGs, where paths coincide with chains and the
min-max is Dilworth's decomposition) to *general* finite DAGs. The governing
result is the standard minimum-path-cover/maximum-matching duality for finite
DAGs via the bipartite double cover, in the path-cover setting of Diestel,
*Graph Theory* §2.5 (the setting of Gallai and Milgram's path-cover theorem
(Diestel, *Graph Theory* §2.5, Theorem 2.5.1), as recorded in the
transitive-DAG development): the minimum number of vertex-disjoint paths
covering all vertices of a finite DAG equals the number of vertices minus the
maximum size of a matching in the bipartite double cover
(`minPathCover_eq_card_sub_ncard_maximum`).

## Why a direct proof

For a general (non-transitive) DAG there is no Dilworth reduction: the minimum
path cover can strictly exceed the reachability width (two sources feeding one
middle vertex feeding two sinks needs three paths but has width two), so
Dilworth's decomposition and Kőnig's theorem govern the *reachability/chain*
version (minimum path cover of the transitive closure). Transitivity of the
DAG is sufficient but not necessary for the two minimum path-cover values to
coincide — e.g. the non-transitive DAG with arcs `0 → 1` and `1 → 2` but no
`0 → 2` has a one-path cover both before and after transitive closure — and
for a non-transitive DAG the values need not coincide. The general-DAG
formula is instead a direct correspondence between path covers and matchings:

* the consecutive arcs of the paths of a cover form a matching, using
  `|V| − (# paths)` arcs (`exists_matching_of_pathCover`);
* the arcs of a matching of size `m` link up into `|V| − m` vertex-disjoint
  paths (`exists_pathCover_of_matching`), since every vertex has at most one
  matched predecessor and one matched successor, and acyclicity rules out
  matched cycles.

The Dilworth/Kőnig connection is recovered for transitive closures: combining
the main theorem with the transitive-DAG development shows the reachability
width equals `|V|` minus the edge count of any maximum matching subgraph of
the reachability double cover
(`width_eq_card_sub_ncard_maximum_transClosure`).

## Representation

Vertices live in a `Fintype`; arcs are a Mathlib `Digraph`. Acyclicity
(`D.IsAcyclic`) is stated as irreflexivity of the transitive closure
(`Relation.TransGen`), which is exactly the usable form: a matched cycle would
be a witness against it. Paths, path covers, and `minPathCoverSize` are reused
from the transitive-DAG development (their definitions never assumed
transitivity). Matchings are developed internally as a `Finset (V × V)` of
arcs with injective projections (a private encoding kept to the proof); the
public interface goes through maximum matching subgraphs of the bipartite
double cover, which is built as a `SimpleGraph (V ⊕ V)` (`doubleCover`) with
its bipartiteness proved (`doubleCover_bipartite`).
-/

variable {V : Type*}

-- `D.IsAcyclic`, `transClosure`, the closure preservations, and
-- `isAcyclic_of_isTransitiveDAG` live in
-- `MathlibExt.Combinatorics.Digraph.PathCover` (opened above).

/-- The bipartite double cover of a digraph: two copies (`Sum.inl` = left,
`Sum.inr` = right) of the vertex set, with a cross edge for each arc. -/
def doubleCover (D : Digraph V) : SimpleGraph (V ⊕ V) where
  Adj := fun x y => match x, y with
    | Sum.inl u, Sum.inr v => D.Adj u v
    | Sum.inr v, Sum.inl u => D.Adj u v
    | _, _ => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact False.elim h
    · exact h
    · exact h
    · exact False.elim h⟩
  loopless := ⟨by
    intro x
    cases x <;> exact not_false⟩

/-- Cross edges of the double cover, left to right. -/
@[simp]
theorem doubleCover_adj_inl_inr (D : Digraph V) (u v : V) :
    (doubleCover D).Adj (Sum.inl u) (Sum.inr v) ↔ D.Adj u v :=
  Iff.rfl

/-- Cross edges of the double cover, right to left. -/
@[simp]
theorem doubleCover_adj_inr_inl (D : Digraph V) (v u : V) :
    (doubleCover D).Adj (Sum.inr v) (Sum.inl u) ↔ D.Adj u v :=
  Iff.rfl

/-- No edges within the left copy. -/
theorem doubleCover_not_adj_inl_inl (D : Digraph V) (u v : V) :
    ¬ (doubleCover D).Adj (Sum.inl u) (Sum.inl v) :=
  fun h => h

/-- No edges within the right copy. -/
theorem doubleCover_not_adj_inr_inr (D : Digraph V) (u v : V) :
    ¬ (doubleCover D).Adj (Sum.inr u) (Sum.inr v) :=
  fun h => h

/-- The double cover is bipartite (left copy vs right copy). -/
theorem doubleCover_bipartite (D : Digraph V) :
    (doubleCover D).IsBipartite := by
  have hdisj : Disjoint (Set.range Sum.inl) (Set.range (Sum.inr : V → V ⊕ V)) := by
    rw [Set.disjoint_left]
    rintro x ⟨u, rfl⟩ ⟨v, hEq⟩
    exact Sum.inr_ne_inl hEq
  have hmem : ∀ x y : V ⊕ V, (doubleCover D).Adj x y →
      (x ∈ Set.range Sum.inl ∧ y ∈ Set.range (Sum.inr : V → V ⊕ V)) ∨
      (x ∈ Set.range (Sum.inr : V → V ⊕ V) ∧ y ∈ Set.range Sum.inl) := by
    intro x y h
    cases x <;> cases y
    · exact absurd h (doubleCover_not_adj_inl_inl D _ _)
    · exact Or.inl ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
    · exact Or.inr ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
    · exact absurd h (doubleCover_not_adj_inr_inr D _ _)
  exact SimpleGraph.IsBipartiteWith.isBipartite ⟨hdisj, hmem⟩

/-- A matching in the double cover, presented as a finset of arcs: every
member is an arc, and both endpoint projections are injective (each vertex has
at most one matched successor and at most one matched predecessor).
Private: the public interface goes through `IsMaximumMatching`. -/
private def IsMatchingArcs (D : Digraph V) (E : Finset (V × V)) : Prop :=
  (∀ e ∈ E, D.Adj e.1 e.2) ∧
    (∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁.1 = e₂.1 → e₁ = e₂) ∧
    (∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁.2 = e₂.2 → e₁ = e₂)

/-- The empty arc set is a matching. -/
private theorem isMatchingArcs_empty (D : Digraph V) : IsMatchingArcs D ∅ := by
  refine ⟨fun e he => absurd he (Finset.notMem_empty e), ?_, ?_⟩ <;>
    intro e₁ he₁
  · exact absurd he₁ (Finset.notMem_empty e₁)
  · exact absurd he₁ (Finset.notMem_empty e₁)

open Classical in
/-- The maximum size of a matching in the bipartite double cover (`0` if no
matching exists, which never happens since the empty matching always
qualifies). Private: the public interface goes through `IsMaximumMatching`. -/
private noncomputable def maxMatchingSize (D : Digraph V) [Fintype V] : ℕ :=
  let all : Finset (Finset (V × V)) := Finset.univ.powerset
  let valid := all.filter fun E => IsMatchingArcs D E
  if h : valid.Nonempty then valid.sup' h fun E => E.card else 0

/-- A matching bounds `maxMatchingSize` from below. -/
private theorem card_le_maxMatchingSize (D : Digraph V) [Fintype V]
    {E : Finset (V × V)}
    (hE : IsMatchingArcs D E) : E.card ≤ maxMatchingSize D := by
  classical
  have hmem : E ∈ Finset.univ.powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ E)
  have hmem' : E ∈ (Finset.univ.powerset.filter
      fun E => IsMatchingArcs D E) :=
    Finset.mem_filter.mpr ⟨hmem, hE⟩
  unfold maxMatchingSize
  change E.card ≤ (if h : ((Finset.univ.powerset.filter
      fun E => IsMatchingArcs D E)).Nonempty
    then ((Finset.univ.powerset.filter
      fun E => IsMatchingArcs D E)).sup' h fun E => E.card else 0)
  rw [dite_eq_left ⟨E, hmem'⟩]
  exact Finset.le_sup' _ hmem'

/-- Some matching attains `maxMatchingSize`. -/
private theorem exists_isMatchingArcs_card_eq_maxMatchingSize (D : Digraph V)
    [Fintype V] :
    ∃ E, IsMatchingArcs D E ∧ E.card = maxMatchingSize D := by
  classical
  have hmem : (∅ : Finset (V × V)) ∈ Finset.univ.powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ ∅)
  have hne : (Finset.univ.powerset.filter
      fun E => IsMatchingArcs D E).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨hmem, isMatchingArcs_empty D⟩⟩
  obtain ⟨E, hEmem, hEeq⟩ := Finset.exists_mem_eq_sup' hne fun E => E.card
  obtain ⟨-, hE⟩ := Finset.mem_filter.mp hEmem
  refine ⟨E, hE, ?_⟩
  unfold maxMatchingSize
  change E.card = (if h : ((Finset.univ.powerset.filter
      fun E => IsMatchingArcs D E)).Nonempty
    then ((Finset.univ.powerset.filter
      fun E => IsMatchingArcs D E)).sup' h fun E => E.card else 0)
  rw [dite_eq_left hne]
  exact hEeq.symm

/-- Consecutive pairs of a vertex list: the arcs used by the path. -/
private def edgesOf : List V → List (V × V)
  | [] => []
  | [_] => []
  | a :: b :: l => (a, b) :: edgesOf (b :: l)

/-- A path on `n` vertices uses `n - 1` arcs. -/
private theorem edgesOf_length (l : List V) :
    (edgesOf l).length = l.length - 1 := by
  cases l with
  | nil => rfl
  | cons a l =>
    cases l with
    | nil => rfl
    | cons b l' =>
      change ((a, b) :: edgesOf (b :: l')).length = (a :: b :: l').length - 1
      rw [List.length_cons, edgesOf_length]
      simp only [List.length_cons]
      omega

/-- First endpoints of used arcs lie on the path. -/
private theorem edgesOf_mem_fst {l : List V} {u v : V}
    (h : (u, v) ∈ edgesOf l) : u ∈ l := by
  cases l with
  | nil => exact absurd h (List.not_mem_nil)
  | cons a l =>
    cases l with
    | nil => exact absurd h (List.not_mem_nil)
    | cons b l' =>
      rw [show edgesOf (a :: b :: l') = (a, b) :: edgesOf (b :: l')
        from rfl] at h
      rcases List.mem_cons.mp h with hEq | hTail
      · obtain ⟨hu, -⟩ := Prod.mk.inj hEq
        subst u
        exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (edgesOf_mem_fst hTail))

/-- Second endpoints of used arcs lie in the tail of the path. -/
private theorem edgesOf_mem_snd_tail {l : List V} {u v : V}
    (h : (u, v) ∈ edgesOf l) : v ∈ l.tail := by
  cases l with
  | nil => exact absurd h (List.not_mem_nil)
  | cons a l =>
    cases l with
    | nil => exact absurd h (List.not_mem_nil)
    | cons b l' =>
      rw [show edgesOf (a :: b :: l') = (a, b) :: edgesOf (b :: l')
        from rfl] at h
      rcases List.mem_cons.mp h with hEq | hTail
      · obtain ⟨-, hv⟩ := Prod.mk.inj hEq
        subst v
        change b ∈ (b :: l')
        exact List.mem_cons.mpr (Or.inl rfl)
      · have hmem := edgesOf_mem_snd_tail hTail
        change v ∈ (b :: l')
        exact List.mem_cons.mpr (Or.inr hmem)

/-- Second endpoints of used arcs lie on the path. -/
private theorem edgesOf_mem_snd {l : List V} {u v : V}
    (h : (u, v) ∈ edgesOf l) : v ∈ l := by
  cases l with
  | nil => exact absurd h (List.not_mem_nil)
  | cons a l =>
    have htail := edgesOf_mem_snd_tail h
    cases l with
    | nil =>
      change v ∈ ([] : List V).tail at htail
      exact absurd htail (List.not_mem_nil)
    | cons b l' =>
      change v ∈ (b :: l') at htail
      exact List.mem_cons.mpr (Or.inr htail)

/-- Used arcs of a chain are arcs of the digraph. -/
private theorem edgesOf_adj {D : Digraph V} {l : List V}
    (hch : List.IsChain D.Adj l) {e : V × V} (he : e ∈ edgesOf l) :
    D.Adj e.1 e.2 := by
  cases l with
  | nil => exact absurd he (List.not_mem_nil)
  | cons a l =>
    cases l with
    | nil => exact absurd he (List.not_mem_nil)
    | cons b l' =>
      rw [List.isChain_cons_cons] at hch
      rw [show edgesOf (a :: b :: l') = (a, b) :: edgesOf (b :: l')
        from rfl] at he
      rcases List.mem_cons.mp he with hEq | hTail
      · subst hEq
        exact hch.1
      · exact edgesOf_adj hch.2 hTail

/-- Within one duplicate-free path, each vertex has at most one successor. -/
private theorem edgesOf_fst_unique {l : List V} (hn : l.Nodup)
    {u v v' : V} (h : (u, v) ∈ edgesOf l) (h' : (u, v') ∈ edgesOf l) :
    v = v' := by
  cases l with
  | nil => exact absurd h (List.not_mem_nil)
  | cons a l =>
    cases l with
    | nil => exact absurd h (List.not_mem_nil)
    | cons b l' =>
      have hn' : (b :: l').Nodup := (List.nodup_cons.mp hn).2
      have hnb : a ∉ b :: l' := (List.nodup_cons.mp hn).1
      rw [show edgesOf (a :: b :: l') = (a, b) :: edgesOf (b :: l')
        from rfl] at h h'
      rcases List.mem_cons.mp h with hEq | hTail <;>
        rcases List.mem_cons.mp h' with hEq' | hTail'
      · obtain ⟨-, hv⟩ := Prod.mk.inj hEq
        obtain ⟨-, hv'⟩ := Prod.mk.inj hEq'
        rw [hv, hv']
      · obtain ⟨hu, -⟩ := Prod.mk.inj hEq
        rw [hu] at hTail'
        exact absurd (edgesOf_mem_fst hTail') hnb
      · obtain ⟨hu, -⟩ := Prod.mk.inj hEq'
        rw [hu] at hTail
        exact absurd (edgesOf_mem_fst hTail) hnb
      · exact edgesOf_fst_unique hn' hTail hTail'

/-- Within one duplicate-free path, each vertex has at most one predecessor. -/
private theorem edgesOf_snd_unique {l : List V} (hn : l.Nodup)
    {u u' v : V} (h : (u, v) ∈ edgesOf l) (h' : (u', v) ∈ edgesOf l) :
    u = u' := by
  cases l with
  | nil => exact absurd h (List.not_mem_nil)
  | cons a l =>
    cases l with
    | nil => exact absurd h (List.not_mem_nil)
    | cons b l' =>
      have hn' : (b :: l').Nodup := (List.nodup_cons.mp hn).2
      have hnb : b ∉ l' := fun hmem =>
        (List.nodup_cons.mp hn').1 hmem
      rw [show edgesOf (a :: b :: l') = (a, b) :: edgesOf (b :: l')
        from rfl] at h h'
      rcases List.mem_cons.mp h with hEq | hTail <;>
        rcases List.mem_cons.mp h' with hEq' | hTail'
      · obtain ⟨hu, -⟩ := Prod.mk.inj hEq
        obtain ⟨hu', -⟩ := Prod.mk.inj hEq'
        rw [hu, hu']
      · obtain ⟨-, hv⟩ := Prod.mk.inj hEq
        rw [hv] at hTail'
        have hmem : b ∈ (b :: l').tail := edgesOf_mem_snd_tail hTail'
        change b ∈ l' at hmem
        exact absurd hmem hnb
      · obtain ⟨-, hv⟩ := Prod.mk.inj hEq'
        rw [hv] at hTail
        have hmem : b ∈ (b :: l').tail := edgesOf_mem_snd_tail hTail
        change b ∈ l' at hmem
        exact absurd hmem hnb
      · exact edgesOf_snd_unique hn' hTail hTail'

/-- The used arcs of a duplicate-free path are duplicate-free. -/
private theorem edgesOf_nodup {l : List V} (hn : l.Nodup) :
    (edgesOf l).Nodup := by
  cases l with
  | nil => exact List.nodup_nil
  | cons a l =>
    cases l with
    | nil => exact List.nodup_nil
    | cons b l' =>
      have hn' : (b :: l').Nodup := (List.nodup_cons.mp hn).2
      have hnb : a ∉ b :: l' := (List.nodup_cons.mp hn).1
      rw [show edgesOf (a :: b :: l') = (a, b) :: edgesOf (b :: l') from rfl,
        List.nodup_cons]
      refine ⟨?_, edgesOf_nodup hn'⟩
      intro hmem
      exact hnb (edgesOf_mem_fst hmem)

/-- Pair-form of successor uniqueness for rewriting. -/
private theorem edgesOf_fst_unique_pair {l : List V} (hn : l.Nodup)
    {e₁ e₂ : V × V} (h₁ : e₁ ∈ edgesOf l) (h₂ : e₂ ∈ edgesOf l)
    (h : e₁.1 = e₂.1) : e₁ = e₂ := by
  obtain ⟨u₁, v₁⟩ := e₁
  obtain ⟨u₂, v₂⟩ := e₂
  have hu : u₁ = u₂ := h
  subst hu
  have hv : v₁ = v₂ := edgesOf_fst_unique hn h₁ h₂
  cases hv
  rfl

/-- Pair-form of predecessor uniqueness for rewriting. -/
private theorem edgesOf_snd_unique_pair {l : List V} (hn : l.Nodup)
    {e₁ e₂ : V × V} (h₁ : e₁ ∈ edgesOf l) (h₂ : e₂ ∈ edgesOf l)
    (h : e₁.2 = e₂.2) : e₁ = e₂ := by
  obtain ⟨u₁, v₁⟩ := e₁
  obtain ⟨u₂, v₂⟩ := e₂
  have hv : v₁ = v₂ := h
  subst hv
  have hu : u₁ = u₂ := edgesOf_snd_unique hn h₁ h₂
  cases hu
  rfl

/-- Every path cover yields a matching with `|V| - (# paths)` arcs: the
consecutive arcs of the paths. No acyclicity is needed — duplicate-free
disjoint chains always give injective endpoint projections. -/
private theorem exists_matching_of_pathCover (D : Digraph V) [Fintype V]
    {P : Finset (Finset V)} (hP : IsPathCover D P) :
    ∃ E, IsMatchingArcs D E ∧ E.card = Fintype.card V - P.card := by
  classical
  have hex : ∀ s : Finset V, ∃ l : List V,
      s ∈ P → l.Nodup ∧ List.IsChain D.Adj l ∧ l.toFinset = s := by
    intro s
    by_cases hs : s ∈ P
    · obtain ⟨l, hN, hC, -, hF⟩ := (hP.1 s hs).1
      exact ⟨l, fun _ => ⟨hN, hC, hF⟩⟩
    · exact ⟨[], fun h => absurd h hs⟩
  choose l hl using hex
  have hlN : ∀ s ∈ P, (l s).Nodup := fun s hs => (hl s hs).1
  have hlC : ∀ s ∈ P, List.IsChain D.Adj (l s) := fun s hs => (hl s hs).2.1
  have hlF : ∀ s ∈ P, (l s).toFinset = s := fun s hs => (hl s hs).2.2
  have hmem_unique : ∀ a : V, ∀ s ∈ P, ∀ t ∈ P, a ∈ s → a ∈ t → s = t := by
    intro a s hs t ht h₁ h₂
    by_contra hne
    have hdisj := hP.2.1 s hs t ht hne
    rw [Finset.disjoint_left] at hdisj
    exact hdisj h₁ h₂
  have hmem_of_mem_edges : ∀ (s : Finset V) (hs : s ∈ P) (e : V × V),
      e ∈ (edgesOf (l s)).toFinset → e.1 ∈ s ∧ e.2 ∈ s := by
    intro s hs e he
    rw [List.mem_toFinset] at he
    have h1 : e.1 ∈ (l s).toFinset :=
      List.mem_toFinset.mpr (edgesOf_mem_fst he)
    have h2 : e.2 ∈ (l s).toFinset :=
      List.mem_toFinset.mpr (edgesOf_mem_snd he)
    rw [hlF s hs] at h1 h2
    exact ⟨h1, h2⟩
  set E : Finset (V × V) :=
    P.biUnion (fun s => (edgesOf (l s)).toFinset) with hE
  have hEadj : ∀ e ∈ E, D.Adj e.1 e.2 := by
    intro e he
    rw [hE, Finset.mem_biUnion] at he
    obtain ⟨s, hs, hse⟩ := he
    rw [List.mem_toFinset] at hse
    exact edgesOf_adj (hlC s hs) hse
  have hEleft : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁.1 = e₂.1 → e₁ = e₂ := by
    intro e₁ he₁ e₂ he₂ hfst
    rw [hE, Finset.mem_biUnion] at he₁ he₂
    obtain ⟨s, hs, hs₁⟩ := he₁
    obtain ⟨t, ht, ht₂⟩ := he₂
    obtain ⟨m₁, -⟩ := hmem_of_mem_edges s hs e₁ hs₁
    obtain ⟨m₂, -⟩ := hmem_of_mem_edges t ht e₂ ht₂
    rw [← hfst] at m₂
    have hst : s = t := hmem_unique e₁.1 s hs t ht m₁ m₂
    subst s
    rw [List.mem_toFinset] at hs₁ ht₂
    exact edgesOf_fst_unique_pair (hlN t ht) hs₁ ht₂ hfst
  have hEright : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁.2 = e₂.2 → e₁ = e₂ := by
    intro e₁ he₁ e₂ he₂ hsnd
    rw [hE, Finset.mem_biUnion] at he₁ he₂
    obtain ⟨s, hs, hs₁⟩ := he₁
    obtain ⟨t, ht, ht₂⟩ := he₂
    obtain ⟨-, m₁⟩ := hmem_of_mem_edges s hs e₁ hs₁
    obtain ⟨-, m₂⟩ := hmem_of_mem_edges t ht e₂ ht₂
    rw [← hsnd] at m₂
    have hst : s = t := hmem_unique e₁.2 s hs t ht m₁ m₂
    subst s
    rw [List.mem_toFinset] at hs₁ ht₂
    exact edgesOf_snd_unique_pair (hlN t ht) hs₁ ht₂ hsnd
  have hcard_each : ∀ s ∈ P, ((edgesOf (l s)).toFinset).card = s.card - 1 := by
    intro s hs
    rw [List.toFinset_card_of_nodup (edgesOf_nodup (hlN s hs)),
      edgesOf_length]
    have hlen : (l s).length = s.card := by
      have h := List.toFinset_card_of_nodup (hlN s hs)
      rw [hlF s hs] at h
      exact h.symm
    rw [hlen]
  have hdisjE : (↑P : Set (Finset V)).PairwiseDisjoint
      (fun s => (edgesOf (l s)).toFinset) := by
    intro s hs t ht hne
    rw [Finset.mem_coe] at hs ht
    change Disjoint ((edgesOf (l s)).toFinset) ((edgesOf (l t)).toFinset)
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    obtain ⟨m₁, -⟩ := hmem_of_mem_edges s hs e he₁
    obtain ⟨m₂, -⟩ := hmem_of_mem_edges t ht e he₂
    exact hne (hmem_unique e.1 s hs t ht m₁ m₂)
  have hsumEq : ∑ s ∈ P, ((edgesOf (l s)).toFinset).card
      = ∑ s ∈ P, (s.card - 1) :=
    Finset.sum_congr rfl (fun s hs => hcard_each s hs)
  have hpos : ∀ s ∈ P, 1 ≤ s.card := fun s hs =>
    Finset.card_pos.mpr (hP.1 s hs).2
  have hadd : ∑ s ∈ P, (s.card - 1) + ∑ s ∈ P, 1
      = ∑ s ∈ P, s.card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have := hpos s hs
    omega
  have hsum1 : ∑ _s ∈ P, 1 = P.card := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]
  have hbiU : P.biUnion id = Finset.univ := by
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_univ, id, iff_true]
    exact hP.2.2 a
  have hdisjP : (↑P : Set (Finset V)).PairwiseDisjoint id := by
    intro s hs t ht hne
    rw [Finset.mem_coe] at hs ht
    change Disjoint (id s) (id t)
    exact hP.2.1 s hs t ht hne
  have hcover : ∑ s ∈ P, s.card = Fintype.card V := by
    have hbc := Finset.card_biUnion hdisjP
    rw [hbiU, Finset.card_univ] at hbc
    have hsumid : ∑ u ∈ P, (id u).card = ∑ s ∈ P, s.card := by
      apply Finset.sum_congr rfl
      intro s _
      rfl
    rw [hsumid] at hbc
    exact hbc.symm
  have hEcard : E.card + P.card = Fintype.card V := by
    rw [hE, Finset.card_biUnion hdisjE, hsumEq, ← hsum1, hadd, hcover]
  refine ⟨E, ⟨hEadj, hEleft, hEright⟩, by omega⟩

open Classical in
/-- Matched successor: the unique `v` with `(u, v) ∈ E`, if any. -/
private noncomputable def nextOf (E : Finset (V × V)) (u : V) : Option V :=
  if h : ∃ v, (u, v) ∈ E then some (Classical.choose h) else none

open Classical in
/-- Matched predecessor: the unique `u` with `(u, v) ∈ E`, if any. -/
private noncomputable def prevOf (E : Finset (V × V)) (v : V) : Option V :=
  if h : ∃ u, (u, v) ∈ E then some (Classical.choose h) else none

/-- A `nextOf` value always comes from a matched arc. -/
private theorem mem_of_nextOf_eq_some {E : Finset (V × V)} {u v : V}
    (h : nextOf E u = some v) : (u, v) ∈ E := by
  unfold nextOf at h
  by_cases hex : ∃ v, (u, v) ∈ E
  · rw [dite_eq_left hex] at h
    have hEq : Classical.choose hex = v := Option.some_inj.mp h
    rw [← hEq]
    exact Classical.choose_spec hex
  · rw [dite_eq_right hex] at h
    simp at h

/-- A `prevOf` value always comes from a matched arc. -/
private theorem mem_of_prevOf_eq_some {E : Finset (V × V)} {u v : V}
    (h : prevOf E v = some u) : (u, v) ∈ E := by
  unfold prevOf at h
  by_cases hex : ∃ u, (u, v) ∈ E
  · rw [dite_eq_left hex] at h
    have hEq : Classical.choose hex = u := Option.some_inj.mp h
    rw [← hEq]
    exact Classical.choose_spec hex
  · rw [dite_eq_right hex] at h
    simp at h

/-- In a matching, a membership determines the successor. -/
private theorem nextOf_eq_some_of_mem {D : Digraph V} {E : Finset (V × V)}
    (hE : IsMatchingArcs D E) {u v : V} (hmem : (u, v) ∈ E) :
    nextOf E u = some v := by
  unfold nextOf
  split_ifs with hex
  · have huniq : Classical.choose hex = v := by
      have hspec := Classical.choose_spec hex
      have hEq := hE.2.1 _ hspec _ hmem rfl
      exact (Prod.mk.inj hEq).2
    rw [huniq]
  · exact absurd ⟨v, hmem⟩ hex

/-- In a matching, a membership determines the predecessor. -/
private theorem prevOf_eq_some_of_mem {D : Digraph V} {E : Finset (V × V)}
    (hE : IsMatchingArcs D E) {u v : V} (hmem : (u, v) ∈ E) :
    prevOf E v = some u := by
  unfold prevOf
  split_ifs with hex
  · have huniq : Classical.choose hex = u := by
      have hspec := Classical.choose_spec hex
      have hEq := hE.2.2 _ hspec _ hmem rfl
      exact (Prod.mk.inj hEq).1
    rw [huniq]
  · exact absurd ⟨u, hmem⟩ hex

/-- Successor and predecessor determine each other. -/
private theorem prevOf_nextOf {D : Digraph V} {E : Finset (V × V)}
    (hE : IsMatchingArcs D E) {u v : V} (h : nextOf E u = some v) :
    prevOf E v = some u :=
  prevOf_eq_some_of_mem hE (mem_of_nextOf_eq_some h)

/-- Predecessor and successor determine each other. -/
private theorem nextOf_prevOf {D : Digraph V} {E : Finset (V × V)}
    (hE : IsMatchingArcs D E) {u v : V} (h : prevOf E v = some u) :
    nextOf E u = some v :=
  nextOf_eq_some_of_mem hE (mem_of_prevOf_eq_some h)

/-- A matched successor is joined by an arc. -/
private theorem adj_of_nextOf {D : Digraph V} {E : Finset (V × V)}
    (hE : IsMatchingArcs D E) {u v : V} (h : nextOf E u = some v) :
    D.Adj u v :=
  hE.1 _ (mem_of_nextOf_eq_some h)

/-- A matched predecessor is joined by an arc. -/
private theorem adj_of_prevOf {D : Digraph V} {E : Finset (V × V)}
    (hE : IsMatchingArcs D E) {u v : V} (h : prevOf E v = some u) :
    D.Adj u v :=
  hE.1 _ (mem_of_prevOf_eq_some h)

open Classical in
/-- Reachability rank: the number of vertices reachable from `v` (itself
included). Strictly decreases along arcs of a DAG, so matched-successor
iteration terminates. -/
private noncomputable def dagRank (D : Digraph V) [Fintype V] (v : V) : ℕ :=
  (Finset.univ.filter fun w => v = w ∨ Relation.TransGen D.Adj v w).card

/-- The rank strictly decreases along arcs of a DAG: everything reachable
from the head is reachable from the tail, but not vice versa (else a cycle).
-/
private theorem dagRank_lt_of_adj (D : Digraph V) [Fintype V] (hD : D.IsAcyclic)
    {u v : V} (h : D.Adj u v) : dagRank D v < dagRank D u := by
  classical
  have hsub : Finset.univ.filter (fun w => v = w ∨ Relation.TransGen D.Adj v w)
      ⊆ Finset.univ.filter (fun w => u = w ∨ Relation.TransGen D.Adj u w) := by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    obtain ⟨-, hw | hw⟩ := hw
    · subst hw
      exact ⟨Finset.mem_univ v, Or.inr (Relation.TransGen.single h)⟩
    · exact ⟨Finset.mem_univ w, Or.inr (Relation.TransGen.head h hw)⟩
  have hmem : u ∈ Finset.univ.filter
        (fun w => u = w ∨ Relation.TransGen D.Adj u w) ∧
      u ∉ Finset.univ.filter
        (fun w => v = w ∨ Relation.TransGen D.Adj v w) := by
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ u, Or.inl rfl⟩
    · rw [Finset.mem_filter]
      intro hmemw
      obtain ⟨-, huv | huv⟩ := hmemw
      · rw [huv] at h
        exact hD u (Relation.TransGen.single h)
      · exact hD u (Relation.TransGen.head h huv)
  have hne : Finset.univ.filter (fun w => v = w ∨ Relation.TransGen D.Adj v w)
      ≠ Finset.univ.filter (fun w => u = w ∨ Relation.TransGen D.Adj u w) := by
    intro heq
    apply hmem.2
    rw [heq]
    exact hmem.1
  unfold dagRank
  exact Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)

set_option linter.unusedVariables false in
/-- Forward matched chain from a vertex, by well-founded recursion on the
reachability rank (matched successors have strictly smaller rank). -/
private noncomputable def chainWF (E : Finset (V × V)) [Fintype V]
    (D : Digraph V) (hD : D.IsAcyclic) (hE : IsMatchingArcs D E) (s : V) :
    List V :=
  match h : nextOf E s with
  | none => [s]
  | some w => s :: chainWF E D hD hE w
termination_by dagRank D s
decreasing_by
  exact dagRank_lt_of_adj D hD (adj_of_nextOf hE h)

/-- The chain starts at its seed. -/
private theorem chainWF_mem_head (E : Finset (V × V)) [Fintype V]
    (D : Digraph V) (hD : D.IsAcyclic) (hE : IsMatchingArcs D E) (s : V) :
    s ∈ chainWF E D hD hE s := by
  refine chainWF.induct_unfolding E D hD hE (fun s r => s ∈ r) ?_ ?_ s
  · intro x hnone
    exact List.mem_singleton.mpr rfl
  · intro x w hsome ih
    exact List.mem_cons.mpr (Or.inl rfl)

/-- Members of the chain are reachable from the seed. -/
private theorem chainWF_mem_reach (E : Finset (V × V)) [Fintype V]
    (D : Digraph V) (hD : D.IsAcyclic) (hE : IsMatchingArcs D E) (s : V)
    {u : V} (hmem : u ∈ chainWF E D hD hE s) :
    u = s ∨ Relation.TransGen D.Adj s u := by
  revert hmem
  refine chainWF.induct_unfolding E D hD hE
    (fun s r => u ∈ r → u = s ∨ Relation.TransGen D.Adj s u) ?_ ?_ s
  · intro x hnone hmem
    rw [List.mem_singleton.mp hmem]
    exact Or.inl rfl
  · intro x w hsome ih hmem
    rw [List.mem_cons] at hmem
    rcases hmem with hEq | htail
    · subst u
      exact Or.inl rfl
    · rcases ih htail with hEq2 | hreach
      · subst u
        exact Or.inr (Relation.TransGen.single (adj_of_nextOf hE hsome))
      · exact Or.inr (Relation.TransGen.head (adj_of_nextOf hE hsome) hreach)

/-- The chain is duplicate-free: a repeat would close a matched directed
cycle, contradicting acyclicity. -/
private theorem chainWF_nodup (E : Finset (V × V)) [Fintype V]
    (D : Digraph V) (hD : D.IsAcyclic) (hE : IsMatchingArcs D E) (s : V) :
    (chainWF E D hD hE s).Nodup := by
  refine chainWF.induct_unfolding E D hD hE (fun s r => r.Nodup) ?_ ?_ s
  · intro x hnone
    exact List.nodup_singleton x
  · intro x w hsome ih
    rw [List.nodup_cons]
    refine ⟨?_, ih⟩
    intro hmem
    rcases chainWF_mem_reach E D hD hE w hmem with hEq | hreach
    · subst w
      exact hD x (Relation.TransGen.single (adj_of_nextOf hE hsome))
    · exact hD x (Relation.TransGen.head (adj_of_nextOf hE hsome) hreach)

/-- The head of the chain is its seed. -/
private theorem chainWF_head (E : Finset (V × V)) [Fintype V]
    (D : Digraph V) (hD : D.IsAcyclic) (hE : IsMatchingArcs D E) (s : V) :
    (chainWF E D hD hE s).head? = some s := by
  refine chainWF.induct_unfolding E D hD hE
    (fun s r => r.head? = some s) ?_ ?_ s
  · intro x hnone
    rfl
  · intro x w hsome ih
    rfl

/-- The chain has consecutive adjacency. -/
private theorem chainWF_isChain (E : Finset (V × V)) [Fintype V]
    (D : Digraph V) (hD : D.IsAcyclic) (hE : IsMatchingArcs D E) (s : V) :
    List.IsChain D.Adj (chainWF E D hD hE s) := by
  refine chainWF.induct_unfolding E D hD hE
    (fun s r => List.IsChain D.Adj r) ?_ ?_ s
  · intro x hnone
    exact List.isChain_singleton x
  · intro x w hsome ih
    cases htail : chainWF E D hD hE w with
    | nil =>
      have hmem := chainWF_mem_head E D hD hE w
      rw [htail] at hmem
      exact absurd hmem List.not_mem_nil
    | cons y l =>
      have hy : y = w := by
        have h1 := chainWF_head E D hD hE w
        rw [htail] at h1
        exact Option.some_inj.mp h1
      subst y
      rw [List.isChain_cons_cons]
      refine ⟨adj_of_nextOf hE hsome, ?_⟩
      rw [← htail]
      exact ih

/-- The chain is successor-closed: members' matched successors stay inside. -/
private theorem chainWF_succ_mem (E : Finset (V × V)) [Fintype V]
    (D : Digraph V) (hD : D.IsAcyclic) (hE : IsMatchingArcs D E) (s : V)
    {u v : V} (hmem : u ∈ chainWF E D hD hE s)
    (hsucc : nextOf E u = some v) : v ∈ chainWF E D hD hE s := by
  revert hmem hsucc
  refine chainWF.induct_unfolding E D hD hE
    (fun s r => u ∈ r → nextOf E u = some v → v ∈ r) ?_ ?_ s
  · intro x hnone hmem hsucc
    rw [List.mem_singleton.mp hmem] at hsucc
    rw [hnone] at hsucc
    simp at hsucc
  · intro x w hsome ih hmem hsucc
    rw [List.mem_cons] at hmem ⊢
    rcases hmem with hEq | htail
    · subst u
      rw [hsome] at hsucc
      have hEq2 : v = w := Option.some_inj.mp hsucc.symm
      subst v
      exact Or.inr (chainWF_mem_head E D hD hE w)
    · exact Or.inr (ih htail hsucc)

set_option linter.unusedVariables false in
/-- Backward root: iterate matched predecessors to the start of the chain.
Terminates since predecessors have strictly larger reachability rank, so
`card - rank` strictly decreases. -/
private noncomputable def backRoot (E : Finset (V × V)) [Fintype V]
    (D : Digraph V) (hD : D.IsAcyclic) (hE : IsMatchingArcs D E) (v : V) : V :=
  match h : prevOf E v with
  | none => v
  | some u => backRoot E D hD hE u
termination_by Fintype.card V - dagRank D v
decreasing_by
  classical
  have hlt : dagRank D v < dagRank D u :=
    dagRank_lt_of_adj D hD (adj_of_prevOf hE h)
  have hle : dagRank D u ≤ Fintype.card V := by
    unfold dagRank
    calc (Finset.univ.filter
            fun w => u = w ∨ Relation.TransGen D.Adj u w).card
          ≤ Finset.univ.card :=
            Finset.card_le_card (Finset.filter_subset _ _)
      _ = Fintype.card V := Finset.card_univ
  omega

/-- The backward root has no matched predecessor: it is a chain start. -/
private theorem backRoot_prev_none (E : Finset (V × V)) [Fintype V]
    (D : Digraph V) (hD : D.IsAcyclic) (hE : IsMatchingArcs D E) (v : V) :
    prevOf E (backRoot E D hD hE v) = none := by
  refine backRoot.induct_unfolding E D hD hE
    (fun v r => prevOf E r = none) ?_ ?_ v
  · intro x hnone
    exact hnone
  · intro x u hsome ih
    exact ih

/-- Every vertex lies on the forward chain from its backward root. -/
private theorem backRoot_mem_chain (E : Finset (V × V)) [Fintype V]
    (D : Digraph V) (hD : D.IsAcyclic) (hE : IsMatchingArcs D E) (v : V) :
    v ∈ chainWF E D hD hE (backRoot E D hD hE v) := by
  refine backRoot.induct_unfolding E D hD hE
    (fun v r => v ∈ chainWF E D hD hE r) ?_ ?_ v
  · intro x hnone
    exact chainWF_mem_head E D hD hE x
  · intro x u hsome ih
    exact chainWF_succ_mem E D hD hE _ ih (nextOf_prevOf hE hsome)

/-- Unfolding equation: no predecessor means fixed point. -/
private theorem backRoot_of_no_prev (E : Finset (V × V)) [Fintype V]
    (D : Digraph V) (hD : D.IsAcyclic) (hE : IsMatchingArcs D E) (v : V)
    (h : prevOf E v = none) : backRoot E D hD hE v = v := by
  revert h
  refine backRoot.induct_unfolding E D hD hE
    (fun v r => prevOf E v = none → r = v) ?_ ?_ v
  · intro x hnone h
    rfl
  · intro x u hsome ih h
    rw [hsome] at h
    simp at h

/-- Unfolding equation: step through the predecessor. -/
private theorem backRoot_of_prev (E : Finset (V × V)) [Fintype V]
    (D : Digraph V) (hD : D.IsAcyclic) (hE : IsMatchingArcs D E) (v : V)
    {u : V} (h : prevOf E v = some u) :
    backRoot E D hD hE v = backRoot E D hD hE u := by
  revert h
  refine backRoot.induct_unfolding E D hD hE
    (fun v r => prevOf E v = some u → r = backRoot E D hD hE u) ?_ ?_ v
  · intro x hnone h
    rw [hnone] at h
    simp at h
  · intro x w hsome ih h
    have hEq : w = u := Option.some_inj.mp (hsome.symm.trans h)
    subst w
    rfl

/-- The backward root is constant along a forward chain. -/
private theorem backRoot_const_on_chain (E : Finset (V × V)) [Fintype V]
    (D : Digraph V) (hD : D.IsAcyclic) (hE : IsMatchingArcs D E) (s : V)
    {u : V} (hmem : u ∈ chainWF E D hD hE s) :
    backRoot E D hD hE u = backRoot E D hD hE s := by
  revert hmem
  refine chainWF.induct_unfolding E D hD hE
    (fun s r => u ∈ r → backRoot E D hD hE u = backRoot E D hD hE s)
    ?_ ?_ s
  · intro x hnone hmem
    rw [List.mem_singleton.mp hmem]
  · intro x w hsome ih hmem
    rw [List.mem_cons] at hmem
    rcases hmem with hEq | htail
    · subst u
      rfl
    · rw [ih htail]
      exact backRoot_of_prev E D hD hE w (prevOf_nextOf hE hsome)

/-- Every matching yields a path cover with `|V| - (# matched arcs)` paths:
the forward chains from the unmatched-predecessor starts. -/
private theorem exists_pathCover_of_matching (D : Digraph V) [Fintype V]
    (hD : D.IsAcyclic) {E : Finset (V × V)} (hE : IsMatchingArcs D E) :
    ∃ P, IsPathCover D P ∧ P.card = Fintype.card V - E.card := by
  classical
  set S : Finset V := Finset.univ.filter (fun v => prevOf E v = none) with hS
  set P : Finset (Finset V) :=
    S.image (fun s => (chainWF E D hD hE s).toFinset) with hP
  have hmemS : ∀ v : V, backRoot E D hD hE v ∈ S := by
    intro v
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, backRoot_prev_none E D hD hE v⟩
  have hroot_self : ∀ s ∈ S, backRoot E D hD hE s = s := by
    intro s hs
    rw [hS, Finset.mem_filter] at hs
    exact backRoot_of_no_prev E D hD hE s hs.2
  have hinj : Set.InjOn (fun s => (chainWF E D hD hE s).toFinset) ↑S := by
    intro x hx y hy hEq
    rw [Finset.mem_coe] at hx hy
    beta_reduce at hEq
    have hxmem : x ∈ chainWF E D hD hE y := by
      have h1 : x ∈ (chainWF E D hD hE x).toFinset :=
        List.mem_toFinset.mpr (chainWF_mem_head E D hD hE x)
      rw [hEq] at h1
      exact List.mem_toFinset.mp h1
    have hconst := backRoot_const_on_chain E D hD hE y hxmem
    rw [hroot_self x hx, hroot_self y hy] at hconst
    exact hconst
  have hPcard : P.card = S.card := by
    rw [hP]
    exact Finset.card_image_of_injOn hinj
  have hTcard : (E.image Prod.snd).card = E.card := by
    apply Finset.card_image_of_injOn
    intro e₁ he₁ e₂ he₂ hEq
    rw [Finset.mem_coe] at he₁ he₂
    exact hE.2.2 e₁ he₁ e₂ he₂ hEq
  have hTS : E.image Prod.snd = Finset.univ \ S := by
    ext v
    rw [Finset.mem_image, Finset.mem_sdiff, hS, Finset.mem_filter]
    constructor
    · rintro ⟨e, heE, hEq⟩
      refine ⟨Finset.mem_univ v, ?_⟩
      intro hcon
      obtain ⟨-, hnone⟩ := hcon
      have hsome := prevOf_eq_some_of_mem hE heE
      rw [hEq] at hsome
      rw [hnone] at hsome
      simp at hsome
    · rintro ⟨-, hcon⟩
      have hne : prevOf E v ≠ none :=
        fun hnone => hcon ⟨Finset.mem_univ v, hnone⟩
      match hprev : prevOf E v with
      | none => exact absurd hprev hne
      | some u => exact ⟨(u, v), mem_of_prevOf_eq_some hprev, rfl⟩
  have hScard : S.card = Fintype.card V - E.card := by
    have hsd := Finset.card_sdiff (s := S) (t := Finset.univ)
    rw [Finset.card_univ, Finset.inter_univ, ← hTS, hTcard] at hsd
    have hle : S.card ≤ Fintype.card V := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ S)
    omega
  have hpaths : ∀ s ∈ P, IsPath D s ∧ s.Nonempty := by
    intro s hs
    rw [hP, Finset.mem_image] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    have hne : chainWF E D hD hE s₀ ≠ [] := by
      intro hempty
      have hmem := chainWF_mem_head E D hD hE s₀
      rw [hempty] at hmem
      exact absurd hmem List.not_mem_nil
    refine ⟨⟨chainWF E D hD hE s₀, chainWF_nodup E D hD hE s₀,
      chainWF_isChain E D hD hE s₀, hne, rfl⟩, ?_⟩
    exact ⟨s₀, List.mem_toFinset.mpr (chainWF_mem_head E D hD hE s₀)⟩
  have hdisj : ∀ s ∈ P, ∀ t ∈ P, s ≠ t → Disjoint s t := by
    intro s hs t ht hne
    rw [hP, Finset.mem_image] at hs ht
    obtain ⟨s₁, hs₁, rfl⟩ := hs
    obtain ⟨s₂, hs₂, rfl⟩ := ht
    rw [Finset.disjoint_left]
    intro a ha₁ ha₂
    rw [List.mem_toFinset] at ha₁ ha₂
    have e1 : backRoot E D hD hE a = s₁ :=
      (backRoot_const_on_chain E D hD hE s₁ ha₁).trans
        (hroot_self s₁ hs₁)
    have e2 : backRoot E D hD hE a = s₂ :=
      (backRoot_const_on_chain E D hD hE s₂ ha₂).trans
        (hroot_self s₂ hs₂)
    have e12 : s₁ = s₂ := e1.symm.trans e2
    exact hne (by rw [e12])
  have hcover : ∀ a : V, ∃ s ∈ P, a ∈ s := by
    intro a
    refine ⟨(chainWF E D hD hE (backRoot E D hD hE a)).toFinset, ?_, ?_⟩
    · rw [hP, Finset.mem_image]
      exact ⟨backRoot E D hD hE a, hmemS a, rfl⟩
    · exact List.mem_toFinset.mpr (backRoot_mem_chain E D hD hE a)
  refine ⟨P, ⟨hpaths, hdisj, hcover⟩, ?_⟩
  rw [hPcard]
  exact hScard

/-- Minimum path cover duality, internal arc-set form: the minimum number of
vertex-disjoint paths covering all vertices of a finite DAG equals the number
of vertices minus the maximum size of a matching in the bipartite double
cover. The two directions are the matching↔path-cover correspondence:
consecutive arcs of cover paths form a matching, and matched arcs link up
into paths (acyclicity ruling out matched cycles). The public form
`minPathCover_eq_card_sub_ncard_maximum` states this through the standard
matching API. -/
private theorem minPathCover_eq_card_sub_maxMatching (D : Digraph V) [Fintype V]
    (hD : D.IsAcyclic) :
    minPathCoverSize D = Fintype.card V - maxMatchingSize D := by
  classical
  obtain ⟨P, hP, hPcard⟩ := exists_isPathCover_card_eq_minPathCoverSize D
  obtain ⟨E₁, hE₁, hE₁card⟩ := exists_matching_of_pathCover D hP
  obtain ⟨E₂, hE₂, hE₂card⟩ := exists_isMatchingArcs_card_eq_maxMatchingSize D
  obtain ⟨P₂, hP₂, hP₂card⟩ := exists_pathCover_of_matching D hD hE₂
  have hle1 := minPathCoverSize_le_card D hP₂
  have hle2 := card_le_maxMatchingSize D hE₁
  omega

/-- The reachability width of a finite DAG equals `|V|` minus the maximum
matching size in the reachability double cover: on the transitive closure,
the matching formula meets Dilworth's decomposition (via the transitive-DAG
development). This is the form in which Dilworth's theorem and Kőnig's
theorem govern the problem; for general DAGs the path cover itself can be
larger than the width. Internal arc-set form; the public corollary
`width_eq_card_sub_ncard_maximum_transClosure` states this through the
standard matching API. -/
private theorem width_eq_card_sub_maxMatching_transClosure (D : Digraph V)
    [Fintype V] (hD : D.IsAcyclic) :
    MathlibExt.Combinatorics.Digraph.PathCoverWanted.maxAntichainSize
        (transClosure D) (isTransitiveDAG_transClosure D hD)
      = Fintype.card V - maxMatchingSize (transClosure D) := by
  have hmain := minPathCover_eq_card_sub_maxMatching (transClosure D)
    (isAcyclic_transClosure D hD)
  have hdil := minPathCover_eq_maxAntichain (transClosure D)
    (isTransitiveDAG_transClosure D hD)
  omega

open MathlibExt.Combinatorics.Matching (IsMaximumMatching exists_maximum_matching)

/-! ## Bridge to the standard matching API

The development above encodes matchings of the double cover as arc sets (a
private encoding). This section connects that encoding — in both directions,
and preserving cardinality — to Mathlib's matching-subgraph API
(`SimpleGraph.Subgraph.IsMatching`) and the repository's maximum-matching API
(`IsMaximumMatching`, `exists_maximum_matching`); the conversions themselves
stay private, and the public endpoints are the headline theorem for ordinary
matching subgraphs (`minPathCover_eq_card_sub_ncard_maximum`) and the width
corollary (`width_eq_card_sub_ncard_maximum_transClosure`), which compose
directly with the existing matching/Kőnig development.
-/

/-- The subgraph of the double cover spanned by a matching arc set: the
vertices are the matched endpoints on each side and the edges are the matched
cross edges. -/
private def subgraphOfMatchingArcs (D : Digraph V) (E : Finset (V × V))
    (hE : IsMatchingArcs D E) : (doubleCover D).Subgraph where
  verts := {x | ∃ u v, (u, v) ∈ E ∧ (x = Sum.inl u ∨ x = Sum.inr v)}
  Adj := fun x y => match x, y with
    | Sum.inl u, Sum.inr v => (u, v) ∈ E
    | Sum.inr v, Sum.inl u => (u, v) ∈ E
    | _, _ => False
  adj_sub := by
    intro x y h
    cases x <;> cases y
    · exact False.elim h
    · exact hE.1 _ h
    · exact hE.1 _ h
    · exact False.elim h
  edge_vert := by
    intro x y h
    cases x <;> cases y
    · exact False.elim h
    · exact ⟨_, _, h, Or.inl rfl⟩
    · exact ⟨_, _, h, Or.inr rfl⟩
    · exact False.elim h
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact False.elim h
    · exact h
    · exact h
    · exact False.elim h⟩

/-- Vertices of the spanned subgraph are the matched endpoints. -/
@[simp]
private theorem mem_verts_subgraphOfMatchingArcs (D : Digraph V)
    (E : Finset (V × V)) (hE : IsMatchingArcs D E) (x : V ⊕ V) :
    x ∈ (subgraphOfMatchingArcs D E hE).verts ↔
      ∃ u v, (u, v) ∈ E ∧ (x = Sum.inl u ∨ x = Sum.inr v) :=
  Iff.rfl

/-- Edges of the spanned subgraph, left to right. -/
@[simp]
private theorem adj_subgraphOfMatchingArcs_inl_inr (D : Digraph V)
    (E : Finset (V × V)) (hE : IsMatchingArcs D E) (u v : V) :
    (subgraphOfMatchingArcs D E hE).Adj (Sum.inl u) (Sum.inr v) ↔
      (u, v) ∈ E :=
  Iff.rfl

/-- Edges of the spanned subgraph, right to left. -/
@[simp]
private theorem adj_subgraphOfMatchingArcs_inr_inl (D : Digraph V)
    (E : Finset (V × V)) (hE : IsMatchingArcs D E) (u v : V) :
    (subgraphOfMatchingArcs D E hE).Adj (Sum.inr v) (Sum.inl u) ↔
      (u, v) ∈ E :=
  Iff.rfl

/-- No edges of the spanned subgraph within the left copy. -/
@[simp]
private theorem adj_subgraphOfMatchingArcs_inl_inl (D : Digraph V)
    (E : Finset (V × V)) (hE : IsMatchingArcs D E) (u v : V) :
    (subgraphOfMatchingArcs D E hE).Adj (Sum.inl u) (Sum.inl v) ↔ False :=
  Iff.rfl

/-- No edges of the spanned subgraph within the right copy. -/
@[simp]
private theorem adj_subgraphOfMatchingArcs_inr_inr (D : Digraph V)
    (E : Finset (V × V)) (hE : IsMatchingArcs D E) (u v : V) :
    (subgraphOfMatchingArcs D E hE).Adj (Sum.inr u) (Sum.inr v) ↔ False :=
  Iff.rfl

/-- The spanned subgraph is a matching in Mathlib's sense: each matched
endpoint sees exactly one neighbor, by endpoint uniqueness. -/
private theorem isMatching_subgraphOfMatchingArcs (D : Digraph V)
    (E : Finset (V × V)) (hE : IsMatchingArcs D E) :
    (subgraphOfMatchingArcs D E hE).IsMatching := by
  intro x hx
  rw [mem_verts_subgraphOfMatchingArcs] at hx
  obtain ⟨u, v, hmem, rfl | rfl⟩ := hx
  · refine ⟨Sum.inr v, hmem, ?_⟩
    · intro w hw
      cases w with
      | inl w =>
        rw [adj_subgraphOfMatchingArcs_inl_inl] at hw
        exact absurd hw not_false
      | inr w =>
        rw [adj_subgraphOfMatchingArcs_inl_inr] at hw
        have hEq := hE.2.1 _ hmem _ hw rfl
        have hv : v = w := (Prod.mk.inj hEq).2
        subst hv
        rfl
  · refine ⟨Sum.inl u, hmem, ?_⟩
    · intro w hw
      cases w with
      | inl w =>
        rw [adj_subgraphOfMatchingArcs_inr_inl] at hw
        have hEq := hE.2.2 _ hmem _ hw rfl
        have hu : u = w := (Prod.mk.inj hEq).1
        subst hu
        rfl
      | inr w =>
        rw [adj_subgraphOfMatchingArcs_inr_inr] at hw
        exact absurd hw not_false

/-- The double-cover edge of an arc. -/
private def arcEdge (e : V × V) : Sym2 (V ⊕ V) :=
  s(Sum.inl e.1, Sum.inr e.2)

open Classical in
/-- The double-cover edges of a matching arc set, as a finset. -/
private noncomputable def matchingEdgesOfArcs (E : Finset (V × V)) :
    Finset (Sym2 (V ⊕ V)) :=
  E.image arcEdge

/-- The edge set of the spanned subgraph is the coercion of the matched edges:
every edge is a matched cross edge, and same-side pairs never occur. -/
private theorem edgeSet_subgraphOfMatchingArcs (D : Digraph V)
    (E : Finset (V × V)) (hE : IsMatchingArcs D E) :
    (subgraphOfMatchingArcs D E hE).edgeSet
      = ↑(matchingEdgesOfArcs E) := by
  classical
  ext e
  refine Sym2.ind (fun a b => ?_) e
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      constructor
      · intro h
        rw [SimpleGraph.Subgraph.mem_edgeSet,
          adj_subgraphOfMatchingArcs_inl_inl] at h
        exact absurd h not_false
      · intro h
        rw [Finset.mem_coe, matchingEdgesOfArcs, Finset.mem_image] at h
        obtain ⟨e, -, hEq⟩ := h
        simp only [arcEdge] at hEq
        rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact absurd h2 Sum.inr_ne_inl
        · exact absurd h2 Sum.inr_ne_inl
    | inr v =>
      constructor
      · intro h
        rw [SimpleGraph.Subgraph.mem_edgeSet,
          adj_subgraphOfMatchingArcs_inl_inr] at h
        rw [Finset.mem_coe, matchingEdgesOfArcs, Finset.mem_image]
        exact ⟨(u, v), h, rfl⟩
      · intro h
        rw [Finset.mem_coe, matchingEdgesOfArcs, Finset.mem_image] at h
        obtain ⟨e, he, hEq⟩ := h
        simp only [arcEdge] at hEq
        rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨h1, h2⟩ | ⟨h1, -⟩
        · have h1' : e.1 = u := (by simpa using h1)
          have h2' : e.2 = v := (by simpa using h2)
          have heEq : e = (u, v) := Prod.ext h1' h2'
          subst heEq
          rw [SimpleGraph.Subgraph.mem_edgeSet,
            adj_subgraphOfMatchingArcs_inl_inr]
          exact he
        · exact absurd h1 Sum.inl_ne_inr
  | inr u =>
    cases b with
    | inl v =>
      constructor
      · intro h
        rw [SimpleGraph.Subgraph.mem_edgeSet,
          adj_subgraphOfMatchingArcs_inr_inl] at h
        rw [Finset.mem_coe, matchingEdgesOfArcs, Finset.mem_image]
        exact ⟨(v, u), h, Sym2.eq_swap⟩
      · intro h
        rw [Finset.mem_coe, matchingEdgesOfArcs, Finset.mem_image] at h
        obtain ⟨e, he, hEq⟩ := h
        simp only [arcEdge] at hEq
        rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨h1, -⟩ | ⟨h1, h2⟩
        · exact absurd h1 Sum.inl_ne_inr
        · have h1' : e.1 = v := (by simpa using h1)
          have h2' : e.2 = u := (by simpa using h2)
          have heEq : e = (v, u) := Prod.ext h1' h2'
          subst heEq
          rw [SimpleGraph.Subgraph.mem_edgeSet,
            adj_subgraphOfMatchingArcs_inr_inl]
          exact he
    | inr v =>
      constructor
      · intro h
        rw [SimpleGraph.Subgraph.mem_edgeSet,
          adj_subgraphOfMatchingArcs_inr_inr] at h
        exact absurd h not_false
      · intro h
        rw [Finset.mem_coe, matchingEdgesOfArcs, Finset.mem_image] at h
        obtain ⟨e, -, hEq⟩ := h
        simp only [arcEdge] at hEq
        rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd h1 Sum.inl_ne_inr
        · exact absurd h1 Sum.inl_ne_inr

/-- The spanned subgraph has one edge per matched arc. -/
private theorem ncard_edgeSet_subgraphOfMatchingArcs (D : Digraph V)
    (E : Finset (V × V)) (hE : IsMatchingArcs D E) :
    (subgraphOfMatchingArcs D E hE).edgeSet.ncard = E.card := by
  classical
  rw [edgeSet_subgraphOfMatchingArcs D E hE, Set.ncard_coe_finset]
  have himg : (matchingEdgesOfArcs E).card = E.card := by
    rw [matchingEdgesOfArcs]
    apply Finset.card_image_of_injOn
    intro e₁ he₁ e₂ he₂ hEq
    rw [Finset.mem_coe] at he₁ he₂
    simp only [arcEdge] at hEq
    rw [Sym2.eq_iff] at hEq
    rcases hEq with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hE.2.1 e₁ he₁ e₂ he₂ ((by simpa using h1))
    · exact absurd h1 Sum.inl_ne_inr
  exact himg

open Classical in
/-- The arc set of a subgraph of the double cover: the left-to-right cross
edges, read back as arcs. -/
private noncomputable def matchingArcsOfSubgraph (D : Digraph V) [Fintype V]
    (M : (doubleCover D).Subgraph) : Finset (V × V) :=
  Finset.univ.filter fun e => M.Adj (Sum.inl e.1) (Sum.inr e.2)

/-- Membership in the arc set is left-to-right adjacency in the subgraph. -/
@[simp]
private theorem mem_matchingArcsOfSubgraph (D : Digraph V) [Fintype V]
    (M : (doubleCover D).Subgraph) (e : V × V) :
    e ∈ matchingArcsOfSubgraph D M ↔ M.Adj (Sum.inl e.1) (Sum.inr e.2) := by
  classical
  simp [matchingArcsOfSubgraph]

/-- A matching subgraph of the double cover yields a matching arc set: edges
lie over arcs, and neighbor uniqueness in the subgraph gives endpoint
uniqueness on each side. -/
private theorem isMatchingArcs_of_isMatching (D : Digraph V) [Fintype V]
    (M : (doubleCover D).Subgraph) (hM : M.IsMatching) :
    IsMatchingArcs D (matchingArcsOfSubgraph D M) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rw [mem_matchingArcsOfSubgraph] at he
    exact M.adj_sub he
  · intro e₁ he₁ e₂ he₂ hfst
    rw [mem_matchingArcsOfSubgraph] at he₁ he₂
    rw [hfst] at he₁
    have hEq := hM.eq_of_adj_left he₁ he₂
    have hsnd : e₁.2 = e₂.2 := (by simpa using hEq)
    exact Prod.ext hfst hsnd
  · intro e₁ he₁ e₂ he₂ hsnd
    rw [mem_matchingArcsOfSubgraph] at he₁ he₂
    rw [← hsnd] at he₂
    have hEq := hM.eq_of_adj_left (M.adj_symm he₁) (M.adj_symm he₂)
    have hfst : e₁.1 = e₂.1 := (by simpa using hEq)
    exact Prod.ext hfst hsnd

/-- The edge set of a subgraph is the coercion of its arc set's matched
edges: every subgraph edge is a cross edge over an arc. -/
private theorem edgeSet_of_isMatching (D : Digraph V) [Fintype V]
    (M : (doubleCover D).Subgraph) :
    M.edgeSet = ↑(matchingEdgesOfArcs (matchingArcsOfSubgraph D M)) := by
  classical
  ext e
  refine Sym2.ind (fun a b => ?_) e
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      constructor
      · intro h
        rw [SimpleGraph.Subgraph.mem_edgeSet] at h
        exact absurd (M.adj_sub h) (doubleCover_not_adj_inl_inl D u v)
      · intro h
        rw [Finset.mem_coe, matchingEdgesOfArcs, Finset.mem_image] at h
        obtain ⟨e, -, hEq⟩ := h
        simp only [arcEdge] at hEq
        rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact absurd h2 Sum.inr_ne_inl
        · exact absurd h2 Sum.inr_ne_inl
    | inr v =>
      constructor
      · intro h
        rw [SimpleGraph.Subgraph.mem_edgeSet] at h
        have hmem : (u, v) ∈ matchingArcsOfSubgraph D M :=
          (mem_matchingArcsOfSubgraph D M (u, v)).mpr h
        rw [Finset.mem_coe, matchingEdgesOfArcs, Finset.mem_image]
        exact ⟨(u, v), hmem, rfl⟩
      · intro h
        rw [Finset.mem_coe, matchingEdgesOfArcs, Finset.mem_image] at h
        obtain ⟨e, he, hEq⟩ := h
        simp only [arcEdge] at hEq
        rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨h1, h2⟩ | ⟨h1, -⟩
        · have h1' : e.1 = u := (by simpa using h1)
          have h2' : e.2 = v := (by simpa using h2)
          have heEq : e = (u, v) := Prod.ext h1' h2'
          subst heEq
          rw [SimpleGraph.Subgraph.mem_edgeSet]
          exact (mem_matchingArcsOfSubgraph D M (u, v)).mp he
        · exact absurd h1 Sum.inl_ne_inr
  | inr u =>
    cases b with
    | inl v =>
      constructor
      · intro h
        rw [SimpleGraph.Subgraph.mem_edgeSet] at h
        have hmem : (v, u) ∈ matchingArcsOfSubgraph D M :=
          (mem_matchingArcsOfSubgraph D M (v, u)).mpr (M.adj_symm h)
        rw [Finset.mem_coe, matchingEdgesOfArcs, Finset.mem_image]
        exact ⟨(v, u), hmem, Sym2.eq_swap⟩
      · intro h
        rw [Finset.mem_coe, matchingEdgesOfArcs, Finset.mem_image] at h
        obtain ⟨e, he, hEq⟩ := h
        simp only [arcEdge] at hEq
        rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨h1, -⟩ | ⟨h1, h2⟩
        · exact absurd h1 Sum.inl_ne_inr
        · have h1' : e.1 = v := (by simpa using h1)
          have h2' : e.2 = u := (by simpa using h2)
          have heEq : e = (v, u) := Prod.ext h1' h2'
          subst heEq
          rw [SimpleGraph.Subgraph.mem_edgeSet]
          exact M.adj_symm ((mem_matchingArcsOfSubgraph D M (v, u)).mp he)
    | inr v =>
      constructor
      · intro h
        rw [SimpleGraph.Subgraph.mem_edgeSet] at h
        exact absurd (M.adj_sub h) (doubleCover_not_adj_inr_inr D u v)
      · intro h
        rw [Finset.mem_coe, matchingEdgesOfArcs, Finset.mem_image] at h
        obtain ⟨e, -, hEq⟩ := h
        simp only [arcEdge] at hEq
        rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd h1 Sum.inl_ne_inr
        · exact absurd h1 Sum.inl_ne_inr

/-- The arc set of a matching subgraph has one arc per subgraph edge. -/
private theorem card_matchingArcsOfSubgraph (D : Digraph V) [Fintype V]
    (M : (doubleCover D).Subgraph) (hM : M.IsMatching) :
    (matchingArcsOfSubgraph D M).card = M.edgeSet.ncard := by
  classical
  have hE := isMatchingArcs_of_isMatching D M hM
  rw [edgeSet_of_isMatching D M, Set.ncard_coe_finset]
  have himg : (matchingEdgesOfArcs (matchingArcsOfSubgraph D M)).card =
      (matchingArcsOfSubgraph D M).card := by
    rw [matchingEdgesOfArcs]
    apply Finset.card_image_of_injOn
    intro e₁ he₁ e₂ he₂ hEq
    rw [Finset.mem_coe] at he₁ he₂
    simp only [arcEdge] at hEq
    rw [Sym2.eq_iff] at hEq
    rcases hEq with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hE.2.1 e₁ he₁ e₂ he₂ ((by simpa using h1))
    · exact absurd h1 Sum.inl_ne_inr
  exact himg.symm

/-- `maxMatchingSize` is the edge count of any maximum matching subgraph of
the double cover: the conversions above transport optimality in both
directions. -/
private theorem maxMatchingSize_eq_ncard_of_isMaximumMatching (D : Digraph V)
    [Fintype V] {M : (doubleCover D).Subgraph}
    (hM : IsMaximumMatching (doubleCover D) M) :
    maxMatchingSize D = M.edgeSet.ncard := by
  classical
  apply le_antisymm
  · obtain ⟨E, hE, hEcard⟩ := exists_isMatchingArcs_card_eq_maxMatchingSize D
    have hsub := hM.le_ncard (isMatching_subgraphOfMatchingArcs D E hE)
    rw [ncard_edgeSet_subgraphOfMatchingArcs D E hE, hEcard] at hsub
    exact hsub
  · have hE := isMatchingArcs_of_isMatching D M hM.isMatching
    have hcard := card_matchingArcsOfSubgraph D M hM.isMatching
    have hle := card_le_maxMatchingSize D hE
    omega

/-- Some maximum matching subgraph of the double cover attains
`maxMatchingSize` as its edge count. -/
private theorem exists_isMaximumMatching_ncard_eq_maxMatchingSize (D : Digraph V)
    [Fintype V] :
    ∃ M : (doubleCover D).Subgraph,
      IsMaximumMatching (doubleCover D) M ∧
        M.edgeSet.ncard = maxMatchingSize D := by
  classical
  obtain ⟨M, hM⟩ := exists_maximum_matching (doubleCover D)
  exact ⟨M, hM, (maxMatchingSize_eq_ncard_of_isMaximumMatching D hM).symm⟩

/-- The standard minimum-path-cover/maximum-matching duality for finite DAGs
via the bipartite double cover: the minimum path cover of a finite DAG equals
the number of vertices minus the edge count of any maximum matching subgraph
of the bipartite double cover. -/
theorem minPathCover_eq_card_sub_ncard_maximum (D : Digraph V) [Fintype V]
    (hD : D.IsAcyclic) {M : (doubleCover D).Subgraph}
    (hM : IsMaximumMatching (doubleCover D) M) :
    minPathCoverSize D = Fintype.card V - M.edgeSet.ncard := by
  rw [minPathCover_eq_card_sub_maxMatching D hD,
    maxMatchingSize_eq_ncard_of_isMaximumMatching D hM]

/-- The reachability width of a finite DAG equals `|V|` minus the edge count
of any maximum matching subgraph of the reachability double cover: on the
transitive closure, the matching formula meets Dilworth's decomposition (via
the transitive-DAG development). This is the form in which Dilworth's theorem
and Kőnig's theorem govern the problem; for general DAGs the path cover
itself can be larger than the width. -/
theorem width_eq_card_sub_ncard_maximum_transClosure (D : Digraph V)
    [Fintype V] (hD : D.IsAcyclic)
    {M : (doubleCover (transClosure D)).Subgraph}
    (hM : IsMaximumMatching (doubleCover (transClosure D)) M) :
    MathlibExt.Combinatorics.Digraph.PathCoverWanted.maxAntichainSize
        (transClosure D) (isTransitiveDAG_transClosure D hD)
      = Fintype.card V - M.edgeSet.ncard := by
  rw [width_eq_card_sub_maxMatching_transClosure D hD,
    maxMatchingSize_eq_ncard_of_isMaximumMatching (transClosure D) hM]

end MathlibExt.Combinatorics.SimpleGraph.PathCoverGeneralWanted
