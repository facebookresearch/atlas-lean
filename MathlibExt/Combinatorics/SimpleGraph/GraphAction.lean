/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_MumfordPeriod.lean`
and
`Definitions/Def_CerednikDrinfeld_BruhatTitsTree.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.PNat.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Group actions on graphs

`CerednikDrinfeld.Mumford.GraphAction G 𝒯` says that `G` acts on the vertices of the simple graph
`𝒯` by graph automorphisms. Such an action restricts to subgroups, pulls back along group
homomorphisms, and induces an action on darts. The quotient darts and vertices
(`QuotEdge`, `QuotVert`) carry the stabilizer width `stabWidth` and the reversal
`quotientReversal`.
-/

@[expose] public section

namespace CerednikDrinfeld
namespace Mumford

open MulAction

/-- An action of `G` on the vertices of a graph `𝒯` by graph automorphisms: every `g` maps
adjacent vertices to adjacent vertices. -/
class GraphAction (G : Type*) [Group G] {W : Type*} [MulAction G W] (𝒯 : SimpleGraph W) :
    Prop where
  smul_adj : ∀ (g : G) {v w : W}, 𝒯.Adj v w → 𝒯.Adj (g • v) (g • w)

variable {G : Type*} [Group G] {W : Type*} [MulAction G W] (𝒯 : SimpleGraph W)

/-- A graph action restricts to every subgroup. -/
instance GraphAction.subgroup (H : Subgroup G) [GraphAction G 𝒯] : GraphAction H 𝒯 :=
  ⟨fun h _ _ hadj => GraphAction.smul_adj (h : G) hadj⟩

/-- A graph action pulls back along a group homomorphism. -/
theorem GraphAction.of_compHom {G' : Type*} [Group G'] (φ : G' →* G) [GraphAction G 𝒯] :
    @GraphAction G' _ W (MulAction.compHom W φ) 𝒯 :=
  @GraphAction.mk G' _ W (MulAction.compHom W φ) 𝒯 fun g _ _ hadj =>
    GraphAction.smul_adj (φ g) hadj

variable [GraphAction G 𝒯]

/-- The induced action on darts (oriented edges). -/
instance dartAction : MulAction G 𝒯.Dart where
  smul g d := ⟨(g • d.fst, g • d.snd), GraphAction.smul_adj g d.adj⟩
  one_smul d := SimpleGraph.Dart.ext _ _ (Prod.ext (one_smul G d.fst) (one_smul G d.snd))
  mul_smul g h d :=
    SimpleGraph.Dart.ext _ _ (Prod.ext (mul_smul g h d.fst) (mul_smul g h d.snd))

@[simp] theorem smul_dart_fst (g : G) (d : 𝒯.Dart) : (g • d).fst = g • d.fst := rfl

@[simp] theorem smul_dart_snd (g : G) (d : 𝒯.Dart) : (g • d).snd = g • d.snd := rfl

theorem smul_dart_symm (g : G) (d : 𝒯.Dart) : (g • d).symm = g • d.symm := rfl

/-- The orbits of `G` on the darts of `𝒯` (the darts of the quotient graph `G \ 𝒯`). -/
abbrev QuotEdge (G : Type*) [Group G] {W : Type*} [MulAction G W] (𝒯 : SimpleGraph W)
    [GraphAction G 𝒯] :=
  orbitRel.Quotient G 𝒯.Dart

/-- The orbits of `G` on the vertices (the vertices of the quotient graph `G \ 𝒯`). -/
abbrev QuotVert (G : Type*) [Group G] (W : Type*) [MulAction G W] := orbitRel.Quotient G W

/-- Translating a dart does not change the cardinality of its stabilizer. -/
theorem card_stabilizer_smul (g : G) (d : 𝒯.Dart) :
    Nat.card (stabilizer G (g • d)) = Nat.card (stabilizer G d) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

variable (G) in
/-- The width of a quotient dart: the cardinality of the stabilizer of a representative, as a
positive natural number (`1` if the stabilizer is infinite). -/
noncomputable def stabWidth (e : QuotEdge G 𝒯) : ℕ+ :=
  Nat.toPNat' (Nat.card (stabilizer G e.out))

theorem stabWidth_mk (d : 𝒯.Dart) :
    stabWidth G 𝒯 (Quotient.mk'' d) = Nat.toPNat' (Nat.card (stabilizer G d)) :=
  congrArg Nat.toPNat' (Nat.card_congr
    (stabilizerEquivStabilizerOfOrbitRel (Quotient.mk_out (s := orbitRel G 𝒯.Dart) d)).toEquiv)

variable (G) in
/-- Reversal of quotient darts. -/
def quotientReversal : QuotEdge G 𝒯 → QuotEdge G 𝒯 :=
  Quotient.map' SimpleGraph.Dart.symm (by rintro _ b ⟨g, rfl⟩; exact ⟨g, rfl⟩)

end Mumford
end CerednikDrinfeld
