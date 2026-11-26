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

/-- Consumer with the original binders: translating a dart preserves the size of its
stabilizer. -/
private theorem exactSource {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W)
    [GraphAction G 𝒯] (g : G) (d : 𝒯.Dart) :
    Nat.card (MulAction.stabilizer G (g • d)) = Nat.card (MulAction.stabilizer G d) :=
  card_stabilizer_smul 𝒯 g d

/-- Permutations act on the complete graph by graph automorphisms. -/
private instance : GraphAction (Equiv.Perm (Fin 3)) (⊤ : SimpleGraph (Fin 3)) :=
  ⟨fun g v w h => (SimpleGraph.top_adj _ _).2 fun e =>
    (SimpleGraph.top_adj v w).1 h (MulAction.injective g e)⟩

/-- The induced dart action moves both endpoints. -/
example (g : Equiv.Perm (Fin 3)) (d : (⊤ : SimpleGraph (Fin 3)).Dart) :
    (g • d).fst = g • d.fst ∧ (g • d).snd = g • d.snd :=
  ⟨smul_dart_fst _ g d, smul_dart_snd _ g d⟩

/-- Higher-universe consumer: graph actions restrict to subgroups. -/
example {G : Type (u + 1)} [Group G] {W : Type u} [MulAction G W] (𝒯 : SimpleGraph W)
    [GraphAction G 𝒯] (H : Subgroup G) (h : H) {v w : W} (hvw : 𝒯.Adj v w) :
    𝒯.Adj (h • v) (h • w) :=
  GraphAction.smul_adj h hvw

/-- Boundary: on the empty graph every action is a graph action, since there is nothing to
preserve. -/
example {G : Type u} [Group G] {W : Type u} [MulAction G W] : GraphAction G (⊥ : SimpleGraph W) :=
  ⟨fun _ _ _ h => h.elim⟩
