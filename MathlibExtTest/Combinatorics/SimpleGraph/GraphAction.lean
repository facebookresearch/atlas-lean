/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.GraphAction
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

open CerednikDrinfeld.Mumford

universe u

/-- Consumer with the original binders: a graph action pulls back along a group homomorphism. -/
private theorem exactSource {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W)
    {G' : Type} [Group G'] (φ : G' →* G) [GraphAction G 𝒯] :
    @GraphAction G' _ W (MulAction.compHom W φ) 𝒯 :=
  GraphAction.of_compHom 𝒯 φ

/-- Higher-universe consumer: graph actions restrict to subgroups. -/
example {G : Type (u + 1)} [Group G] {W : Type u} [MulAction G W] (𝒯 : SimpleGraph W)
    [GraphAction G 𝒯] (H : Subgroup G) (h : H) {v w : W} (hvw : 𝒯.Adj v w) :
    𝒯.Adj (h • v) (h • w) :=
  GraphAction.smul_adj h hvw

/-- Permutations act on a complete graph by graph automorphisms. -/
private instance {α : Type*} : GraphAction (Equiv.Perm α) (⊤ : SimpleGraph α) :=
  ⟨fun g v w h => (SimpleGraph.top_adj _ _).2 fun e =>
    (SimpleGraph.top_adj v w).1 h (MulAction.injective g e)⟩

/-- `ℤ` acts on the one-edge graph through `n ↦ swap ^ n`, the pullback of the permutation
action. -/
example : @GraphAction (Multiplicative ℤ) _ Bool
    (MulAction.compHom Bool (zpowersHom (Equiv.Perm Bool) (Equiv.swap false true)))
    (⊤ : SimpleGraph Bool) :=
  GraphAction.of_compHom _ _

/-! Dart orbits need not be the darts of a simple quotient graph. `Equiv.Perm Bool` swaps the
two endpoints of the single edge of `⊤ : SimpleGraph Bool`: there is one vertex orbit and one
dart orbit, and `quotientReversal` fixes that dart orbit, while a simple graph on one vertex has
no darts. -/

/-- The endpoint swap leaves a single vertex orbit. -/
private theorem subsingleton_quotVert_swap : Subsingleton (QuotVert (Equiv.Perm Bool) Bool) :=
  ⟨fun x y => Quotient.inductionOn₂' x y fun a b =>
    Quotient.sound' ⟨Equiv.swap b a, Equiv.swap_apply_left b a⟩⟩

/-- The endpoint swap leaves a single dart orbit. -/
private theorem subsingleton_quotEdge_swap :
    Subsingleton (QuotEdge (Equiv.Perm Bool) (⊤ : SimpleGraph Bool)) := by
  refine ⟨fun x y => Quotient.inductionOn₂' x y fun d e => Quotient.sound' ?_⟩
  refine ⟨Equiv.swap e.fst d.fst, ?_⟩
  obtain ⟨⟨a, b⟩, hab⟩ := d
  obtain ⟨⟨a', b'⟩, hab'⟩ := e
  rw [SimpleGraph.top_adj] at hab hab'
  refine SimpleGraph.Dart.ext _ _ (Prod.ext ?_ ?_)
  · exact Equiv.swap_apply_left a' a
  · change Equiv.swap a' a b' = b
    revert a b a' b'
    decide

/-- The endpoint swap inverts the edge, so `quotientReversal` fixes its dart orbit. -/
example (q : QuotEdge (Equiv.Perm Bool) (⊤ : SimpleGraph Bool)) :
    quotientReversal (Equiv.Perm Bool) ⊤ q = q :=
  subsingleton_quotEdge_swap.elim _ _

/-- One vertex orbit and one dart orbit: the quotient of the endpoint swap is a single vertex
with a single dart orbit above it. -/
example (v w : QuotVert (Equiv.Perm Bool) Bool)
    (e f : QuotEdge (Equiv.Perm Bool) (⊤ : SimpleGraph Bool)) : v = w ∧ e = f :=
  ⟨subsingleton_quotVert_swap.elim v w, subsingleton_quotEdge_swap.elim e f⟩

/-- A simple graph on one vertex has no darts. -/
example (𝒢 : SimpleGraph Unit) : IsEmpty 𝒢.Dart :=
  ⟨fun d => d.adj.ne (Subsingleton.elim _ _)⟩

/-- Boundary: on the empty graph every action is a graph action, since there is nothing to
preserve. -/
example {G : Type u} [Group G] {W : Type u} [MulAction G W] : GraphAction G (⊥ : SimpleGraph W) :=
  ⟨fun _ _ _ h => h.elim⟩
