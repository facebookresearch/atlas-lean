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

public import MathlibExt.Combinatorics.SimpleGraph.SeparatorAPI

@[expose] public section

open MathlibExt.Combinatorics.SimpleGraph.SeparatorAPI
open MathlibExt.Combinatorics.Graph.Fans
open MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted

-- Separated terminal sets are disjoint.
example {V : Type*} {G : SimpleGraph V} {A B : Set V} {X : Finset V}
    (h : IsSeparatorAB G A B X) : Disjoint A B :=
  h.disjointAB

-- Separation is symmetric in the terminal sets.
example {V : Type*} {G : SimpleGraph V} {A B : Set V} {X : Finset V}
    (h : IsSeparatorAB G A B X) : IsSeparatorAB G B A X :=
  h.symm

-- No edge joins separated terminal sets.
example {V : Type*} {G : SimpleGraph V} {A B : Set V} {X : Finset V}
    (h : IsSeparatorAB G A B X) {a b : V} (ha : a ∈ A) (hb : b ∈ B) :
    ¬ G.Adj a b :=
  h.not_adj_of_mem ha hb

-- Core projection: every separator hits every `A–B` walk.
example {V : Type*} {G : SimpleGraph V} {A B : Set V} {X : Finset V}
    (h : IsSeparatorAB G A B X) : SeparatesAB G A B X :=
  h.toSeparatesAB

-- Core monotonicity in the terminal sets needs no disjointness.
example {V : Type*} {G : SimpleGraph V} {A A' B : Set V} {X : Finset V}
    (hsub : A' ⊆ A) (h : SeparatesAB G A B X) : SeparatesAB G A' B X :=
  h.mono_left hsub

example {V : Type*} {G : SimpleGraph V} {A B B' : Set V} {X : Finset V}
    (hsub : B' ⊆ B) (h : SeparatesAB G A B X) : SeparatesAB G A B' X :=
  h.mono_right hsub

-- Core monotonicity in the separator set needs no disjointness.
example {V : Type*} {G : SimpleGraph V} {A B : Set V} {X Y : Finset V}
    (hsub : X ⊆ Y) (h : SeparatesAB G A B X) : SeparatesAB G A B Y :=
  h.mono_sep hsub

-- Core symmetry in the terminal sets.
example {V : Type*} {G : SimpleGraph V} {A B : Set V} {X : Finset V}
    (h : SeparatesAB G A B X) : SeparatesAB G B A X :=
  h.symm

-- Core path-hitting: every `A–B` path meets every walk-hitting set.
example {V : Type*} {G : SimpleGraph V} {A B : Set V} {X : Finset V}
    (h : SeparatesAB G A B X) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (p : G.Path a b) : ∃ v ∈ p.val.support, v ∈ X :=
  h.hit_path ha hb p

-- Wrapper monotonicity is derived from the core.
example {V : Type*} {G : SimpleGraph V} {A A' B : Set V} {X : Finset V}
    (hsub : A' ⊆ A) (h : IsSeparatorAB G A B X) : IsSeparatorAB G A' B X :=
  h.mono_left hsub

example {V : Type*} {G : SimpleGraph V} {A B B' : Set V} {X : Finset V}
    (hsub : B' ⊆ B) (h : IsSeparatorAB G A B X) : IsSeparatorAB G A B' X :=
  h.mono_right hsub

example {V : Type*} {G : SimpleGraph V} {A B : Set V} {X Y : Finset V}
    (hsub : X ⊆ Y) (hdisj : Disjoint (↑Y : Set V) (A ∪ B))
    (h : IsSeparatorAB G A B X) : IsSeparatorAB G A B Y :=
  h.mono_sep hsub hdisj

-- Singleton terminals recover `s-t` vertex cuts.
example {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (C : Finset V) :
    IsSeparatorAB G {s} {t} C ↔ IsSTVertexCut G s t C :=
  isSeparatorAB_singleton_iff_isSTVertexCut G s t C

-- A left singleton recovers the fan separator predicate.
example {V : Type*} (G : SimpleGraph V) (a : V) (B : Set V) (C : Finset V) :
    IsSeparatorAB G {a} B C ↔
      SeparatesVertexFromSet G a B C ∧ Disjoint (↑C : Set V) B :=
  isSeparatorAB_singleton_left_iff_separatesVertexFromSet G a B C

-- The empty set separates iff no `A`-vertex can reach a `B`-vertex.
example {V : Type*} (G : SimpleGraph V) (A B : Set V) :
    IsSeparatorAB G A B ∅ ↔ ∀ a b : V, a ∈ A → b ∈ B → ¬ G.Reachable a b :=
  isSeparatorAB_empty_iff G A B

-- One-walk counting case: a single `A–B` walk forces every separator to be
-- nonempty (pairwise disjointness is vacuous for one walk).
example {V : Type*} {G : SimpleGraph V} {A B : Set V} {X : Finset V}
    (ends : Fin 1 → V × V) (hA : ∀ i, (ends i).1 ∈ A) (hB : ∀ i, (ends i).2 ∈ B)
    (Q : ∀ i, G.Walk (ends i).1 (ends i).2) (hsep : IsSeparatorAB G A B X) :
    1 ≤ X.card :=
  hsep.card_le_of_disjointWalks ends hA hB Q
    (fun i j hne => (hne ((Fin.eq_zero i).trans (Fin.eq_zero j).symm)).elim)

-- One-path counting case.
example {V : Type*} {G : SimpleGraph V} {A B : Set V} {X : Finset V}
    (ends : Fin 1 → V × V) (hA : ∀ i, (ends i).1 ∈ A) (hB : ∀ i, (ends i).2 ∈ B)
    (P : ∀ i, G.Path (ends i).1 (ends i).2) (hsep : IsSeparatorAB G A B X) :
    1 ≤ X.card :=
  hsep.card_le_of_disjointPaths ends hA hB P
    (fun i j hne => (hne ((Fin.eq_zero i).trans (Fin.eq_zero j).symm)).elim)
