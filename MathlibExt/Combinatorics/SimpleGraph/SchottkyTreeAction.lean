/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_SchottkyTreeAction.lean`,
`Definitions/Def_CerednikDrinfeld_MumfordPeriod.lean`
and
`Definitions/Def_CerednikDrinfeld_Ribbon.lean`
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

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.GroupTheory.GroupAction.Quotient

import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace CerednikDrinfeld

variable {E V : Type*}

/-- Degeneracy data for a graph: two endpoint maps from edges to vertices,
together with a positive width for every edge. -/
structure DegeneracyData (E V : Type*) where
  /-- The first endpoint of an edge. -/
  a : E → V
  /-- The second endpoint of an edge. -/
  b : E → V
  /-- The width of an edge. -/
  w : E → ℕ+

namespace Mumford

open MulAction

variable {G : Type*} [Group G] {W : Type*} [MulAction G W] (𝒯 : SimpleGraph W)

/-- An action of a group `G` on the vertex set of a graph `𝒯` that preserves
adjacency. -/
class GraphAction (G : Type*) [Group G] {W : Type*} [MulAction G W] (𝒯 : SimpleGraph W) :
    Prop where
  /-- Adjacent vertices stay adjacent after applying a group element. -/
  smul_adj : ∀ (g : G) {v w : W}, 𝒯.Adj v w → 𝒯.Adj (g • v) (g • w)

variable [GraphAction G 𝒯]

instance dartAction : MulAction G 𝒯.Dart where
  smul g d := ⟨(g • d.fst, g • d.snd), GraphAction.smul_adj g d.adj⟩
  one_smul d := SimpleGraph.Dart.ext _ _ (Prod.ext (one_smul G d.fst) (one_smul G d.snd))
  mul_smul g h d := SimpleGraph.Dart.ext _ _ (Prod.ext (mul_smul g h d.fst) (mul_smul g h d.snd))

@[simp] theorem smul_dart_fst (g : G) (d : 𝒯.Dart) : (g • d).fst = g • d.fst := rfl

@[simp] theorem smul_dart_snd (g : G) (d : 𝒯.Dart) : (g • d).snd = g • d.snd := rfl

theorem smul_dart_symm (g : G) (d : 𝒯.Dart) : (g • d).symm = g • d.symm := rfl

/-- The set of orbits of darts of `𝒯` under `G`: the edge set of the quotient
graph. -/
abbrev QuotEdge (G : Type*) [Group G] {W : Type*} [MulAction G W] (𝒯 : SimpleGraph W)
    [GraphAction G 𝒯] :=
  orbitRel.Quotient G 𝒯.Dart

/-- The set of orbits of vertices of `𝒯` under `G`: the vertex set of the
quotient graph. -/
abbrev QuotVert (G : Type*) [Group G] (W : Type*) [MulAction G W] := orbitRel.Quotient G W

theorem card_stabilizer_smul (g : G) (d : 𝒯.Dart) :
    Nat.card (stabilizer G (g • d)) = Nat.card (stabilizer G d) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

variable (G) in
/-- The width of a quotient edge: the cardinality of the stabilizer of any
dart above it. -/
def stabWidth (e : QuotEdge G 𝒯) : ℕ+ :=
  Nat.toPNat' (Nat.card (stabilizer G e.out))

theorem stabWidth_mk (d : 𝒯.Dart) :
    stabWidth G 𝒯 (Quotient.mk'' d) = Nat.toPNat' (Nat.card (stabilizer G d)) :=
  congrArg Nat.toPNat' (Nat.card_congr
    (stabilizerEquivStabilizerOfOrbitRel (Quotient.mk_out (s := orbitRel G 𝒯.Dart) d)).toEquiv)

variable (G) in
/-- The degeneracy data of the quotient graph: endpoints are the endpoint
orbits, and widths are dart stabilizer cardinalities. -/
def quotientDegeneracyData : DegeneracyData (QuotEdge G 𝒯) (QuotVert G W) where
  a := Quotient.map' (fun d : 𝒯.Dart => d.fst) (by rintro _ b ⟨g, rfl⟩; exact ⟨g, rfl⟩)
  b := Quotient.map' (fun d : 𝒯.Dart => d.snd) (by rintro _ b ⟨g, rfl⟩; exact ⟨g, rfl⟩)
  w := stabWidth G 𝒯

variable (G) in
/-- The reversal of a quotient edge, induced by dart reversal. -/
def quotientReversal : QuotEdge G 𝒯 → QuotEdge G 𝒯 :=
  Quotient.map' SimpleGraph.Dart.symm (by rintro _ b ⟨g, rfl⟩; exact ⟨g, rfl⟩)

variable (G) in
/-- A group acting on a graph is a tree lattice if the action is faithful,
every vertex stabilizer is finite, and the quotient graph has finitely many
vertices and edges. -/
structure IsTreeLattice : Prop where
  /-- The action is faithful. -/
  faithful : FaithfulSMul G W
  /-- Every vertex stabilizer is finite. -/
  finite_stabilizer : ∀ w : W, Finite (stabilizer G w)
  /-- The quotient vertex set is finite. -/
  finite_quotVert : Finite (QuotVert G W)
  /-- The quotient edge set is finite. -/
  finite_quotEdge : Finite (QuotEdge G 𝒯)

variable (G) in
/-- A group acting on a graph is a Schottky group if every vertex stabilizer
is trivial, no group element sends a dart to its reverse, and the quotient
graph has finitely many vertices and edges. -/
structure IsSchottky : Prop where
  /-- Every vertex stabilizer is trivial. -/
  stabilizer_eq_bot : ∀ w : W, stabilizer G w = ⊥
  /-- No group element sends a dart to its reverse. -/
  smul_ne_symm : ∀ (g : G) (d : 𝒯.Dart), g • d ≠ d.symm
  /-- The quotient vertex set is finite. -/
  finite_quotVert : Finite (QuotVert G W)
  /-- The quotient edge set is finite. -/
  finite_quotEdge : Finite (QuotEdge G 𝒯)

theorem stabilizer_dart_le (d : 𝒯.Dart) : stabilizer G d ≤ stabilizer G d.fst := by
  intro g hg
  rw [mem_stabilizer_iff] at hg ⊢
  rw [← smul_dart_fst 𝒯 g d, hg]

namespace IsSchottky

variable {𝒯}

theorem stabilizer_dart_eq_bot (h : IsSchottky G 𝒯) (d : 𝒯.Dart) : stabilizer G d = ⊥ :=
  le_bot_iff.mp ((stabilizer_dart_le 𝒯 d).trans (h.stabilizer_eq_bot d.fst).le)

theorem stabWidth_eq_one (h : IsSchottky G 𝒯) (e : QuotEdge G 𝒯) : stabWidth G 𝒯 e = 1 := by
  induction e using Quotient.inductionOn' with
  | h d => rw [stabWidth_mk, h.stabilizer_dart_eq_bot d, Subgroup.card_bot]; rfl

theorem quotientDegeneracyData_w (h : IsSchottky G 𝒯) (e : QuotEdge G 𝒯) :
    (quotientDegeneracyData G 𝒯).w e = 1 :=
  h.stabWidth_eq_one e

theorem isTreeLattice [Nonempty W] (h : IsSchottky G 𝒯) : IsTreeLattice G 𝒯 where
  faithful := ⟨fun {g₁ g₂} hg => by
    obtain ⟨w⟩ := ‹Nonempty W›
    have : g₂⁻¹ * g₁ ∈ stabilizer G w := by
      rw [mem_stabilizer_iff, mul_smul, hg w, inv_smul_smul]
    rw [h.stabilizer_eq_bot w, Subgroup.mem_bot] at this
    exact (eq_of_inv_mul_eq_one this).symm⟩
  finite_stabilizer w := by rw [h.stabilizer_eq_bot w]; infer_instance
  finite_quotVert := h.finite_quotVert
  finite_quotEdge := h.finite_quotEdge

end IsSchottky

namespace IsTreeLattice

variable {𝒯}

@[reducible] def fintypeQuotVert (h : IsTreeLattice G 𝒯) : Fintype (QuotVert G W) :=
  @Fintype.ofFinite _ h.finite_quotVert

@[reducible] def fintypeQuotEdge (h : IsTreeLattice G 𝒯) : Fintype (QuotEdge G 𝒯) :=
  @Fintype.ofFinite _ h.finite_quotEdge

end IsTreeLattice

/-- Two actions of groups `G` and `H` on `W` agree through a homomorphism
`ρ : G →* H`. -/
def ActsThrough (W : Type*) {G H : Type*} [Group G] [Group H] [MulAction G W] [MulAction H W]
    (ρ : G →* H) : Prop :=
  ∀ (g : G) (w : W), g • w = ρ g • w

variable {𝒯} in
/-- The graph automorphism given by the action of `g : G`. -/
def smulHom (g : G) : 𝒯 →g 𝒯 where
  toFun w := g • w
  map_rel' h := GraphAction.smul_adj g h

@[simp] theorem smulHom_apply (g : G) (w : W) : smulHom (𝒯 := 𝒯) g w = g • w := rfl

@[simp] theorem smulHom_mapDart (g : G) (d : 𝒯.Dart) : (smulHom g).mapDart d = g • d := rfl

theorem quotEdge_mk_smul (g : G) (d : 𝒯.Dart) :
    (Quotient.mk (orbitRel G 𝒯.Dart) (g • d) : QuotEdge G 𝒯) =
      Quotient.mk (orbitRel G 𝒯.Dart) d :=
  Quotient.sound (mem_orbit d g)

/-- The index of a dart relative to a quotient edge: `1` if the dart lies
over the edge, `-1` if its reverse does, and `0` otherwise. -/
def dartIndex [DecidableEq (QuotEdge G 𝒯)] (q : QuotEdge G 𝒯) (d : 𝒯.Dart) : ℤ :=
  (if Quotient.mk (orbitRel G 𝒯.Dart) d = q then 1 else 0) -
    (if Quotient.mk (orbitRel G 𝒯.Dart) d.symm = q then 1 else 0)

/-- The cycle of a walk in the quotient graph: for each label in `E`, the
sum of dart indices of the walk's darts over that quotient edge. -/
def walkCycle [DecidableEq (QuotEdge G 𝒯)] {E : Type*} (orb : E → QuotEdge G 𝒯) {u v : W}
    (p : 𝒯.Walk u v) :
    E → ℤ :=
  fun e => (p.darts.map (dartIndex 𝒯 (orb e))).sum

variable {𝒯} in
/-- A chosen path between two reachable vertices. -/
def somePath {u v : W} (h : 𝒯.Reachable u v) : 𝒯.Path u v := by
  classical exact h.some.toPath

open scoped Classical in
/-- The cycle of the chosen path from `v₀` to `g • v₀`, or zero if they are
not reachable. -/
def pathCycle [DecidableEq (QuotEdge G 𝒯)] {E : Type*} (orb : E → QuotEdge G 𝒯) (v₀ : W)
    (g : G) : E → ℤ :=
  if h : 𝒯.Reachable v₀ (g • v₀) then walkCycle 𝒯 orb (somePath h : 𝒯.Walk v₀ (g • v₀)) else 0

section lemmas

variable [DecidableEq (QuotEdge G 𝒯)] {E : Type*} (orb : E → QuotEdge G 𝒯)

theorem dartIndex_symm (q : QuotEdge G 𝒯) (d : 𝒯.Dart) :
    dartIndex 𝒯 q d.symm = -dartIndex 𝒯 q d := by
  rw [dartIndex, dartIndex, SimpleGraph.Dart.symm_symm]; ring

theorem dartIndex_smul (q : QuotEdge G 𝒯) (g : G) (d : 𝒯.Dart) :
    dartIndex 𝒯 q (g • d) = dartIndex 𝒯 q d := by
  rw [dartIndex, dartIndex, smul_dart_symm, quotEdge_mk_smul, quotEdge_mk_smul]

@[simp] theorem walkCycle_nil (u : W) :
    walkCycle 𝒯 orb (SimpleGraph.Walk.nil : 𝒯.Walk u u) = 0 := by
  funext e; simp [walkCycle]

theorem walkCycle_cons {u v w : W} (h : 𝒯.Adj u v) (p : 𝒯.Walk v w) (e : E) :
    walkCycle 𝒯 orb (SimpleGraph.Walk.cons h p) e =
      dartIndex 𝒯 (orb e) ⟨(u, v), h⟩ + walkCycle 𝒯 orb p e := by
  simp [walkCycle]

theorem walkCycle_append {u v w : W} (p : 𝒯.Walk u v) (q : 𝒯.Walk v w) :
    walkCycle 𝒯 orb (p.append q) = walkCycle 𝒯 orb p + walkCycle 𝒯 orb q := by
  funext e; simp [walkCycle, SimpleGraph.Walk.darts_append, List.sum_append]

theorem walkCycle_reverse {u v : W} (p : 𝒯.Walk u v) :
    walkCycle 𝒯 orb p.reverse = -walkCycle 𝒯 orb p := by
  funext e
  simp only [walkCycle, SimpleGraph.Walk.darts_reverse, List.map_reverse, List.sum_reverse,
    List.map_map, Pi.neg_apply]
  induction p.darts with
  | nil => simp
  | cons d l ih => simp only [List.map_cons, List.sum_cons, Function.comp_apply, ih,
      dartIndex_symm]; ring

theorem walkCycle_map_smulHom {u v : W} (g : G) (p : 𝒯.Walk u v) :
    walkCycle 𝒯 orb (p.map (smulHom g)) = walkCycle 𝒯 orb p := by
  funext e
  simp only [walkCycle, SimpleGraph.Walk.darts_map, List.map_map]
  congr 1
  exact List.map_congr_left fun d _ => by rw [Function.comp_apply, smulHom_mapDart, dartIndex_smul]

theorem pathCycle_eq_walkCycle (hac : 𝒯.IsAcyclic) (v₀ : W) (g : G) (p : 𝒯.Path v₀ (g • v₀)) :
    pathCycle 𝒯 orb v₀ g = walkCycle 𝒯 orb (p : 𝒯.Walk v₀ (g • v₀)) := by
  rw [pathCycle, dif_pos p.1.reachable, hac.path_unique (somePath p.1.reachable) p]

theorem pathCycle_of_not_reachable (v₀ : W) (g : G) (h : ¬𝒯.Reachable v₀ (g • v₀)) :
    pathCycle 𝒯 orb v₀ g = 0 := by
  rw [pathCycle, dif_neg h]

end lemmas

end Mumford

end CerednikDrinfeld

end
