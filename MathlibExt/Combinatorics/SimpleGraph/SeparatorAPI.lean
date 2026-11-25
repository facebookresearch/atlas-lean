/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `2a4dcd009357b93b103d542487dfaa3fa6765d77`.

Original formalization by vonbers (@vonbo) and Avocado; ported with attribution.
Source: formal-math commit `00c3c61d7b9e` (PR #6336).
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import MathlibExt.Combinatorics.Graph.Fans
public import MathlibExt.Combinatorics.Graph.MengerVertex
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card

@[expose] public section

section
namespace MathlibExt.Combinatorics.SimpleGraph.SeparatorAPI

open _root_.SimpleGraph
open MathlibExt.Combinatorics.Graph.Fans

/-!
# A–B separators in simple graphs

Reusable interface for vertex sets separating two terminal sets `A` and `B`.

## Endpoint convention

The walk-hitting core `SeparatesAB G A B X` only asks that `X` meet the support
of **every** `A–B` walk (endpoints included), with **no** endpoint restrictions.
Endpoint avoidance is a separate hypothesis: `IsSeparatorAB G A B X` adds
**disjointness of `X` from `A ∪ B`**.  Because of the disjointness requirement,
a hit can never be an endpoint outside degenerate cases, so this is effectively
internal hitting; as a consequence, separators can only exist when `A` and `B`
are disjoint (`IsSeparatorAB.disjointAB`) with no edges between them
(`IsSeparatorAB.not_adj_of_mem`). The core API (`SeparatesAB.mono_left`,
`SeparatesAB.mono_right`, `SeparatesAB.mono_sep`, `SeparatesAB.symm`,
`SeparatesAB.hit_path`) needs no disjointness; the `IsSeparatorAB` wrappers
are derived from it via `IsSeparatorAB.toSeparatesAB`.

Singleton terminal sets recover MathlibExt's `s-t` vertex cuts
(`isSeparatorAB_singleton_iff_isSTVertexCut`), via the walk-hitting
characterization `MengerVertexWanted.isSTVertexCut_iff_walkSeparator`; a left
singleton recovers the fan separator predicate
(`isSeparatorAB_singleton_left_iff_separatesVertexFromSet`).

We do **not** prove the full A–B max-min duality here (Menger's classical A–B
duality theorem, not yet formalized in this file); we only prove the cheap
counting direction: `k` pairwise-disjoint `A–B` walks force every separator to
have cardinality at least `k`.
-/

/-- `X` meets every `A–B` walk. This is the walk-hitting core shared by the
separator predicates in this file; it imposes no endpoint restrictions. -/
def SeparatesAB {V : Type*} (G : SimpleGraph V) (A B : Set V) (X : Finset V) : Prop :=
  ∀ a b : V, a ∈ A → b ∈ B → ∀ p : G.Walk a b, ∃ v ∈ p.support, v ∈ X

/-- `X` separates `A` from `B`: `X` is disjoint from `A ∪ B` (endpoint
avoidance) and meets every `A–B` walk (the `SeparatesAB` core). -/
def IsSeparatorAB {V : Type*} (G : SimpleGraph V) (A B : Set V) (X : Finset V) : Prop :=
  Disjoint (↑X : Set V) (A ∪ B) ∧ SeparatesAB G A B X

/-- Named projection to the walk-hitting core. -/
theorem IsSeparatorAB.toSeparatesAB {V : Type*} {G : SimpleGraph V} {A B : Set V}
    {X : Finset V} (h : IsSeparatorAB G A B X) : SeparatesAB G A B X :=
  h.2

/-- The walk-hitting core is antitone in the left terminal set. -/
theorem SeparatesAB.mono_left {V : Type*} {G : SimpleGraph V} {A A' B : Set V}
    {X : Finset V} (hsub : A' ⊆ A) (h : SeparatesAB G A B X) :
    SeparatesAB G A' B X :=
  fun a b ha hb p => h a b (hsub ha) hb p

/-- The walk-hitting core is antitone in the right terminal set. -/
theorem SeparatesAB.mono_right {V : Type*} {G : SimpleGraph V} {A B B' : Set V}
    {X : Finset V} (hsub : B' ⊆ B) (h : SeparatesAB G A B X) :
    SeparatesAB G A B' X :=
  fun a b ha hb p => h a b ha (hsub hb) p

/-- The walk-hitting core is monotone in the separator set, with no
disjointness hypothesis. -/
theorem SeparatesAB.mono_sep {V : Type*} {G : SimpleGraph V} {A B : Set V}
    {X Y : Finset V} (hsub : X ⊆ Y) (h : SeparatesAB G A B X) :
    SeparatesAB G A B Y := by
  intro a b ha hb p
  obtain ⟨v, hv, hvX⟩ := h a b ha hb p
  exact ⟨v, hv, hsub hvX⟩

/-- The walk-hitting core is symmetric in the terminal sets. -/
theorem SeparatesAB.symm {V : Type*} {G : SimpleGraph V} {A B : Set V}
    {X : Finset V} (h : SeparatesAB G A B X) : SeparatesAB G B A X := by
  intro b a hb ha q
  obtain ⟨v, hv, hvX⟩ := h a b ha hb q.reverse
  rw [SimpleGraph.Walk.support_reverse] at hv
  exact ⟨v, List.mem_reverse.mp hv, hvX⟩

/-- Every `A–B` path meets every walk-hitting set. -/
theorem SeparatesAB.hit_path {V : Type*} {G : SimpleGraph V} {A B : Set V}
    {X : Finset V} (h : SeparatesAB G A B X)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : G.Path a b) :
    ∃ v ∈ p.val.support, v ∈ X :=
  h a b ha hb p.val

/-- Separator vertices avoid `A`. -/
theorem IsSeparatorAB.not_mem_left {V : Type*} {G : SimpleGraph V} {A B : Set V}
    {X : Finset V} (h : IsSeparatorAB G A B X) {x : V} (hx : x ∈ X) : x ∉ A := by
  have hX : x ∈ (↑X : Set V) := Finset.mem_coe.mpr hx
  have hnot := Set.disjoint_left.mp h.1 hX
  intro hxA
  exact hnot (Set.mem_union_left B hxA)

/-- Separator vertices avoid `B`. -/
theorem IsSeparatorAB.not_mem_right {V : Type*} {G : SimpleGraph V} {A B : Set V}
    {X : Finset V} (h : IsSeparatorAB G A B X) {x : V} (hx : x ∈ X) : x ∉ B := by
  have hX : x ∈ (↑X : Set V) := Finset.mem_coe.mpr hx
  have hnot := Set.disjoint_left.mp h.1 hX
  intro hxB
  exact hnot (Set.mem_union_right A hxB)

/-- Separators are antitone in the left terminal set. -/
theorem IsSeparatorAB.mono_left {V : Type*} {G : SimpleGraph V} {A A' B : Set V}
    {X : Finset V} (hsub : A' ⊆ A) (h : IsSeparatorAB G A B X) :
    IsSeparatorAB G A' B X :=
  ⟨h.1.mono_right (Set.union_subset_union hsub (fun _ hx => hx)),
    h.toSeparatesAB.mono_left hsub⟩

/-- Separators are antitone in the right terminal set. -/
theorem IsSeparatorAB.mono_right {V : Type*} {G : SimpleGraph V} {A B B' : Set V}
    {X : Finset V} (hsub : B' ⊆ B) (h : IsSeparatorAB G A B X) :
    IsSeparatorAB G A B' X :=
  ⟨h.1.mono_right (Set.union_subset_union (fun _ hx => hx) hsub),
    h.toSeparatesAB.mono_right hsub⟩

/-- Separators are monotone in the separator set, provided the larger set stays
disjoint from the terminals (a larger set could otherwise meet `A ∪ B`). -/
theorem IsSeparatorAB.mono_sep {V : Type*} {G : SimpleGraph V} {A B : Set V}
    {X Y : Finset V} (hsub : X ⊆ Y) (hdisj : Disjoint (↑Y : Set V) (A ∪ B))
    (h : IsSeparatorAB G A B X) :
    IsSeparatorAB G A B Y :=
  ⟨hdisj, h.toSeparatesAB.mono_sep hsub⟩

/-- Separation is symmetric in the terminal sets. -/
theorem IsSeparatorAB.symm {V : Type*} {G : SimpleGraph V} {A B : Set V}
    {X : Finset V} (h : IsSeparatorAB G A B X) : IsSeparatorAB G B A X :=
  ⟨by rw [Set.union_comm B A]; exact h.1, h.toSeparatesAB.symm⟩

/-- Every `A–B` path meets every `A–B` separator. -/
theorem IsSeparatorAB.hit_path {V : Type*} {G : SimpleGraph V} {A B : Set V}
    {X : Finset V} (h : IsSeparatorAB G A B X)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : G.Path a b) :
    ∃ v ∈ p.val.support, v ∈ X :=
  h.toSeparatesAB.hit_path ha hb p

/-- Separated terminal sets are disjoint: a common vertex would give the trivial
walk, which no set disjoint from `A ∪ B` can hit. -/
theorem IsSeparatorAB.disjointAB {V : Type*} {G : SimpleGraph V} {A B : Set V}
    {X : Finset V} (h : IsSeparatorAB G A B X) : Disjoint A B := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  obtain ⟨v, hv, hvX⟩ := h.toSeparatesAB x x hxA hxB SimpleGraph.Walk.nil
  rw [SimpleGraph.Walk.support_nil] at hv
  simp only [List.mem_singleton] at hv
  subst hv
  exact h.not_mem_left hvX hxA

/-- No edge joins separated terminal sets: an edge gives a two-vertex walk that a
set disjoint from `A ∪ B` cannot hit. -/
theorem IsSeparatorAB.not_adj_of_mem {V : Type*} {G : SimpleGraph V} {A B : Set V}
    {X : Finset V} (h : IsSeparatorAB G A B X)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B) : ¬ G.Adj a b := by
  intro hadj
  obtain ⟨v, hv, hvX⟩ :=
    h.toSeparatesAB a b ha hb (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
  rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact h.not_mem_left hvX ha
  · exact h.not_mem_right hvX hb

/-- The empty set separates `A` from `B` iff no `A`-vertex can reach a `B`-vertex.
Both directions are proved (reachability is walk-existence by definition). -/
theorem isSeparatorAB_empty_iff {V : Type*} (G : SimpleGraph V) (A B : Set V) :
    IsSeparatorAB G A B ∅ ↔ ∀ a b : V, a ∈ A → b ∈ B → ¬ G.Reachable a b := by
  constructor
  · rintro ⟨-, hhit⟩ a b ha hb ⟨p⟩
    obtain ⟨v, -, hv⟩ := hhit a b ha hb p
    exact Finset.notMem_empty v hv
  · intro hno
    refine ⟨by simp, fun a b ha hb p => ?_⟩
    exact (hno a b ha hb ⟨p⟩).elim

/-- Walk-hitting core at singleton terminals: `SeparatesAB` on `{s}, {t}`
says every `s-t` walk meets `X`. -/
theorem separatesAB_singleton_iff {V : Type*} (G : SimpleGraph V) (s t : V)
    (X : Finset V) :
    SeparatesAB G {s} {t} X ↔
      ∀ p : G.Walk s t, ∃ v ∈ p.support, v ∈ X := by
  constructor
  · intro h p
    exact h s t (Set.mem_singleton s) (Set.mem_singleton t) p
  · intro h a b ha hb p
    rw [Set.mem_singleton_iff] at ha hb
    subst ha
    subst hb
    exact h p

/-- Walk-hitting core at a left singleton: `SeparatesAB` on `{a}, B` says every
walk from `a` to a vertex of `B` meets `X`. -/
theorem separatesAB_singleton_left_iff {V : Type*} (G : SimpleGraph V) (a : V)
    (B : Set V) (X : Finset V) :
    SeparatesAB G {a} B X ↔
      ∀ b ∈ B, ∀ p : G.Walk a b, ∃ v ∈ p.support, v ∈ X := by
  constructor
  · intro h b hb p
    exact h a b (Set.mem_singleton a) hb p
  · intro h x b hx hb p
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h b hb p

/-- A left singleton recovers the fan separator predicate: separating `{a}`
from `B` is separating `a` from `B` in the fan sense plus disjointness from
`B` (the fan predicate only asks `a ∉ C`). -/
theorem isSeparatorAB_singleton_left_iff_separatesVertexFromSet {V : Type*}
    (G : SimpleGraph V) (a : V) (B : Set V) (C : Finset V) :
    IsSeparatorAB G {a} B C ↔
      SeparatesVertexFromSet G a B C ∧ Disjoint (↑C : Set V) B := by
  constructor
  · rintro ⟨hdisj, hcore⟩
    have haC : a ∉ C := by
      intro hcon
      have hC : a ∈ (↑C : Set V) := Finset.mem_coe.mpr hcon
      exact Set.disjoint_left.mp hdisj hC
        (Set.mem_union_left _ (Set.mem_singleton a))
    refine ⟨⟨haC, (separatesAB_singleton_left_iff G a B C).mp hcore⟩,
      hdisj.mono_right Set.subset_union_right⟩
  · rintro ⟨⟨haC, hhit⟩, hdisjB⟩
    refine ⟨?_, (separatesAB_singleton_left_iff G a B C).mpr hhit⟩
    rw [Set.disjoint_left]
    intro x hx hU
    rw [Finset.mem_coe] at hx
    rw [Set.mem_union, Set.mem_singleton_iff] at hU
    rcases hU with rfl | hB
    · exact haC hx
    · exact Set.disjoint_left.mp hdisjB (Finset.mem_coe.mpr hx) hB

/-- Singleton terminal sets recover `s-t` vertex cuts, in both directions. -/
theorem isSeparatorAB_singleton_iff_isSTVertexCut {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V)
    (C : Finset V) :
    IsSeparatorAB G {s} {t} C ↔
      MengerVertexWanted.IsSTVertexCut G s t C := by
  rw [MengerVertexWanted.isSTVertexCut_iff_walkSeparator]
  constructor
  · rintro ⟨hdisj, hcore⟩
    have hs : s ∉ C := by
      intro hcon
      have hC : s ∈ (↑C : Set V) := Finset.mem_coe.mpr hcon
      exact Set.disjoint_left.mp hdisj hC (Set.mem_union_left _ (Set.mem_singleton s))
    have ht : t ∉ C := by
      intro hcon
      have hC : t ∈ (↑C : Set V) := Finset.mem_coe.mpr hcon
      exact Set.disjoint_left.mp hdisj hC (Set.mem_union_right _ (Set.mem_singleton t))
    exact ⟨hs, ht, (separatesAB_singleton_iff G s t C).mp hcore⟩
  · rintro ⟨hs, ht, hhit⟩
    refine ⟨?_, (separatesAB_singleton_iff G s t C).mpr hhit⟩
    rw [Set.disjoint_left]
    intro x hx hU
    rw [Finset.mem_coe] at hx
    rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_singleton_iff] at hU
    rcases hU with rfl | rfl
    · exact hs hx
    · exact ht hx

/-- Menger-flavored counting bound: `k` pairwise-disjoint `A–B` walks (distinct
walks sharing only vertices of `A ∪ B`) force every `A–B` separator to have
cardinality at least `k`. -/
theorem IsSeparatorAB.card_le_of_disjointWalks {V : Type*} {G : SimpleGraph V}
    {A B : Set V} {X : Finset V} {k : ℕ} (ends : Fin k → V × V)
    (hA : ∀ i, (ends i).1 ∈ A) (hB : ∀ i, (ends i).2 ∈ B)
    (Q : ∀ i, G.Walk (ends i).1 (ends i).2)
    (hdisj : ∀ i j, i ≠ j → ∀ v, v ∈ (Q i).support → v ∈ (Q j).support → v ∈ A ∪ B)
    (hsep : IsSeparatorAB G A B X) : k ≤ X.card := by
  classical
  choose f hfmem hfX using (fun i => hsep.toSeparatesAB _ _ (hA i) (hB i) (Q i))
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hmem : f i ∈ (Q j).support := by rw [hij]; exact hfmem j
    have hAB := hdisj i j hne (f i) (hfmem i) hmem
    have hX : f i ∈ (↑X : Set V) := Finset.mem_coe.mpr (hfX i)
    exact (Set.disjoint_left.mp hsep.1 hX hAB).elim
  have hcard : (Finset.image f Finset.univ).card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hsub : Finset.image f Finset.univ ⊆ X := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hfX i
  calc k = (Finset.image f Finset.univ).card := hcard.symm
    _ ≤ X.card := Finset.card_le_card hsub

/-- Path-family version of the counting bound: `k` pairwise-disjoint `A–B` paths
force every `A–B` separator to have cardinality at least `k`. -/
theorem IsSeparatorAB.card_le_of_disjointPaths {V : Type*} {G : SimpleGraph V}
    {A B : Set V} {X : Finset V} {k : ℕ} (ends : Fin k → V × V)
    (hA : ∀ i, (ends i).1 ∈ A) (hB : ∀ i, (ends i).2 ∈ B)
    (P : ∀ i, G.Path (ends i).1 (ends i).2)
    (hdisj : ∀ i j, i ≠ j → ∀ v, v ∈ (P i).val.support →
      v ∈ (P j).val.support → v ∈ A ∪ B)
    (hsep : IsSeparatorAB G A B X) : k ≤ X.card :=
  hsep.card_le_of_disjointWalks ends hA hB (fun i => (P i).val) hdisj

end MathlibExt.Combinatorics.SimpleGraph.SeparatorAPI
end
