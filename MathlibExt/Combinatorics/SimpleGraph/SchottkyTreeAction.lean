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

/-- **Degeneracy data.** Two endpoint maps from a set of edges to a set of vertices, together
with a positive width for every edge. -/
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

/-- **Graph action.** An action of a group `G` on the vertex set of a graph `𝒯` that preserves
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

/-- **Oriented quotient edges.** The set of orbits of darts of `𝒯` under `G`: the oriented
edges of the quotient graph. An edge of `𝒯` has two darts, one for each orientation. When no
element of `G` sends one to the other, they lie in two orbits and the quotient keeps both
orientations: for the translation action of `ℤ` on the integer path graph, the quotient has
one vertex and one unoriented loop, but two oriented edges. When some element of `G` inverts
the edge, that is, sends one of its darts to the reverse dart, both darts lie in one orbit,
which `quotientReversal` fixes. -/
abbrev QuotEdge (G : Type*) [Group G] {W : Type*} [MulAction G W] (𝒯 : SimpleGraph W)
    [GraphAction G 𝒯] :=
  orbitRel.Quotient G 𝒯.Dart

/-- **Quotient vertices.** The set of orbits of vertices of `𝒯` under `G`: the vertex set of
the quotient graph. -/
abbrev QuotVert (G : Type*) [Group G] (W : Type*) [MulAction G W] := orbitRel.Quotient G W

theorem card_stabilizer_smul (g : G) (d : 𝒯.Dart) :
    Nat.card (stabilizer G (g • d)) = Nat.card (stabilizer G d) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

variable (G) in
/-- **Width of an oriented quotient edge.** The cardinality of the stabilizer of any dart
above it. It is defined only when every dart stabilizer is finite, so that the width is the
actual, positive cardinality. -/
def stabWidth (hfin : ∀ d : 𝒯.Dart, Finite (stabilizer G d)) (e : QuotEdge G 𝒯) : ℕ+ :=
  ⟨Nat.card (stabilizer G e.out), @Nat.card_pos _ _ (hfin e.out)⟩

theorem coe_stabWidth_mk (hfin : ∀ d : 𝒯.Dart, Finite (stabilizer G d)) (d : 𝒯.Dart) :
    (stabWidth G 𝒯 hfin (Quotient.mk'' d) : ℕ) = Nat.card (stabilizer G d) :=
  Nat.card_congr
    (stabilizerEquivStabilizerOfOrbitRel (Quotient.mk_out (s := orbitRel G 𝒯.Dart) d)).toEquiv

variable (G) in
/-- **Degeneracy data of the quotient graph.** It is indexed by the oriented edges (the dart
orbits): a dart orbit runs from the orbit of the first vertex of its darts to the orbit of
their second vertex, and its width is the cardinality of a dart stabilizer, which requires
every dart stabilizer to be finite. -/
def quotientDegeneracyData (hfin : ∀ d : 𝒯.Dart, Finite (stabilizer G d)) :
    DegeneracyData (QuotEdge G 𝒯) (QuotVert G W) where
  a := Quotient.map' (fun d : 𝒯.Dart => d.fst) (by rintro _ b ⟨g, rfl⟩; exact ⟨g, rfl⟩)
  b := Quotient.map' (fun d : 𝒯.Dart => d.snd) (by rintro _ b ⟨g, rfl⟩; exact ⟨g, rfl⟩)
  w := stabWidth G 𝒯 hfin

variable (G) in
/-- **Reversal of oriented quotient edges.** The map induced by dart reversal. It fixes
exactly the dart orbits of the edges that some element of `G` inverts
(`quotientReversal_mk_eq_self_iff`). -/
def quotientReversal : QuotEdge G 𝒯 → QuotEdge G 𝒯 :=
  Quotient.map' SimpleGraph.Dart.symm (by rintro _ b ⟨g, rfl⟩; exact ⟨g, rfl⟩)

@[simp] theorem quotientReversal_mk (d : 𝒯.Dart) :
    quotientReversal G 𝒯 (Quotient.mk'' d) = Quotient.mk'' d.symm := rfl

theorem quotientReversal_mk_eq_self_iff (d : 𝒯.Dart) :
    quotientReversal G 𝒯 (Quotient.mk'' d) = Quotient.mk'' d ↔ ∃ g : G, g • d = d.symm := by
  rw [quotientReversal_mk, Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

variable (G) in
/-- **Uniform tree lattice.** A group acting on a tree is a uniform tree lattice if the action
is faithful, every vertex stabilizer is finite, and the quotient graph is finite, with finitely
many vertex orbits and dart orbits. Only the uniform (cocompact) case is covered: a general
tree lattice need only have finite covolume, the sum of `1 / |stabilizer G v|` over the vertex
orbits, and its quotient graph can be infinite. -/
structure IsUniformTreeLattice : Prop where
  /-- The graph is a tree. -/
  isTree : 𝒯.IsTree
  /-- The action is faithful. -/
  faithful : FaithfulSMul G W
  /-- Every vertex stabilizer is finite. -/
  finite_stabilizer : ∀ w : W, Finite (stabilizer G w)
  /-- The quotient vertex set is finite. -/
  finite_quotVert : Finite (QuotVert G W)
  /-- The set of oriented quotient edges (dart orbits) is finite. -/
  finite_quotEdge : Finite (QuotEdge G 𝒯)

variable (G) in
/-- **Schottky group.** A group acting on a tree is a Schottky group if every vertex stabilizer
is trivial, no group element sends a dart to its reverse, and the quotient graph is finite,
with finitely many vertex orbits and dart orbits. -/
structure IsSchottky : Prop where
  /-- The graph is a tree. -/
  isTree : 𝒯.IsTree
  /-- Every vertex stabilizer is trivial. -/
  stabilizer_eq_bot : ∀ w : W, stabilizer G w = ⊥
  /-- No group element sends a dart to its reverse. -/
  smul_ne_symm : ∀ (g : G) (d : 𝒯.Dart), g • d ≠ d.symm
  /-- The quotient vertex set is finite. -/
  finite_quotVert : Finite (QuotVert G W)
  /-- The set of oriented quotient edges (dart orbits) is finite. -/
  finite_quotEdge : Finite (QuotEdge G 𝒯)

theorem stabilizer_dart_le (d : 𝒯.Dart) : stabilizer G d ≤ stabilizer G d.fst := by
  intro g hg
  rw [mem_stabilizer_iff] at hg ⊢
  rw [← smul_dart_fst 𝒯 g d, hg]

namespace IsSchottky

variable {𝒯}

theorem stabilizer_dart_eq_bot (h : IsSchottky G 𝒯) (d : 𝒯.Dart) : stabilizer G d = ⊥ :=
  le_bot_iff.mp ((stabilizer_dart_le 𝒯 d).trans (h.stabilizer_eq_bot d.fst).le)

theorem finite_stabilizer_dart (h : IsSchottky G 𝒯) (d : 𝒯.Dart) : Finite (stabilizer G d) := by
  rw [h.stabilizer_dart_eq_bot d]; infer_instance

theorem stabWidth_eq_one (h : IsSchottky G 𝒯) (hfin : ∀ d : 𝒯.Dart, Finite (stabilizer G d))
    (e : QuotEdge G 𝒯) : stabWidth G 𝒯 hfin e = 1 := by
  induction e using Quotient.inductionOn' with
  | h d =>
    apply PNat.coe_injective
    rw [coe_stabWidth_mk, h.stabilizer_dart_eq_bot d, Subgroup.card_bot]; rfl

theorem quotientDegeneracyData_w (h : IsSchottky G 𝒯)
    (hfin : ∀ d : 𝒯.Dart, Finite (stabilizer G d)) (e : QuotEdge G 𝒯) :
    (quotientDegeneracyData G 𝒯 hfin).w e = 1 :=
  h.stabWidth_eq_one hfin e

theorem isUniformTreeLattice (h : IsSchottky G 𝒯) : IsUniformTreeLattice G 𝒯 where
  isTree := h.isTree
  faithful := ⟨fun {g₁ g₂} hg => by
    obtain ⟨w⟩ := h.isTree.connected.nonempty
    have : g₂⁻¹ * g₁ ∈ stabilizer G w := by
      rw [mem_stabilizer_iff, mul_smul, hg w, inv_smul_smul]
    rw [h.stabilizer_eq_bot w, Subgroup.mem_bot] at this
    exact (eq_of_inv_mul_eq_one this).symm⟩
  finite_stabilizer w := by rw [h.stabilizer_eq_bot w]; infer_instance
  finite_quotVert := h.finite_quotVert
  finite_quotEdge := h.finite_quotEdge

end IsSchottky

namespace IsUniformTreeLattice

variable {𝒯}

theorem finite_stabilizer_dart (h : IsUniformTreeLattice G 𝒯) (d : 𝒯.Dart) :
    Finite (stabilizer G d) := by
  have := h.finite_stabilizer d.fst
  exact Finite.of_injective _ (Subgroup.inclusion_injective (stabilizer_dart_le 𝒯 d))

/-- **Finite quotient vertex set.** The `Fintype` structure on the quotient vertex set of a
uniform tree lattice, which is finite. -/
@[reducible] def fintypeQuotVert (h : IsUniformTreeLattice G 𝒯) : Fintype (QuotVert G W) :=
  @Fintype.ofFinite _ h.finite_quotVert

/-- **Finite set of oriented quotient edges.** The `Fintype` structure on the set of oriented
quotient edges (dart orbits) of a uniform tree lattice, which is finite. -/
@[reducible] def fintypeQuotEdge (h : IsUniformTreeLattice G 𝒯) : Fintype (QuotEdge G 𝒯) :=
  @Fintype.ofFinite _ h.finite_quotEdge

end IsUniformTreeLattice

/-- **Actions agreeing through a homomorphism.** Two actions of groups `G` and `H` on `W`
agree through a homomorphism `ρ : G →* H`: `g • w = ρ g • w` for every `g : G` and `w : W`. -/
def ActsThrough (W : Type*) {G H : Type*} [Group G] [Group H] [MulAction G W] [MulAction H W]
    (ρ : G →* H) : Prop :=
  ∀ (g : G) (w : W), g • w = ρ g • w

variable {𝒯} in
/-- **Action of a group element on the graph.** The graph homomorphism `𝒯 →g 𝒯` given by the
action of `g : G`. -/
def smulHom (g : G) : 𝒯 →g 𝒯 where
  toFun w := g • w
  map_rel' h := GraphAction.smul_adj g h

@[simp] theorem smulHom_apply (g : G) (w : W) : smulHom (𝒯 := 𝒯) g w = g • w := rfl

@[simp] theorem smulHom_mapDart (g : G) (d : 𝒯.Dart) : (smulHom g).mapDart d = g • d := rfl

theorem quotEdge_mk_smul (g : G) (d : 𝒯.Dart) :
    (Quotient.mk (orbitRel G 𝒯.Dart) (g • d) : QuotEdge G 𝒯) =
      Quotient.mk (orbitRel G 𝒯.Dart) d :=
  Quotient.sound (mem_orbit d g)

/-- **Index of a dart relative to an oriented quotient edge.** The indicator of the dart
lying over `q` minus the indicator of its reverse lying over `q`. It is `1` if the dart lies
over `q` and its reverse does not, `-1` if the reverse does and the dart does not, and `0`
otherwise. In particular it is `0` on both darts of an edge that some element of `G` inverts:
the dart and its reverse then lie in one orbit, and the two indicators cancel
(`dartIndex_eq_zero_of_smul_eq_symm`). -/
def dartIndex [DecidableEq (QuotEdge G 𝒯)] (q : QuotEdge G 𝒯) (d : 𝒯.Dart) : ℤ :=
  (if Quotient.mk (orbitRel G 𝒯.Dart) d = q then 1 else 0) -
    (if Quotient.mk (orbitRel G 𝒯.Dart) d.symm = q then 1 else 0)

/-- **Signed edge counts of a walk.** For each label `e : E`, the signed count of the walk's
darts over the oriented quotient edge `orb e`, that is, the sum of their indices relative to
`orb e`: a dart over `orb e` counts `1`, a dart whose reverse lies over it counts `-1`, and the
darts of an edge that `G` inverts count `0`. The endpoints of the walk are arbitrary, so its
image in the quotient graph need not be closed: under the trivial action on a single edge, the
one-step walk has count `1` and joins two different vertex orbits. `pathCycle` is the closed
case. -/
def walkCycle [DecidableEq (QuotEdge G 𝒯)] {E : Type*} (orb : E → QuotEdge G 𝒯) {u v : W}
    (p : 𝒯.Walk u v) :
    E → ℤ :=
  fun e => (p.darts.map (dartIndex 𝒯 (orb e))).sum

variable {𝒯} in
/-- **Chosen path between reachable vertices.** A path between two reachable vertices, chosen
by `Classical.choice`. -/
def somePath {u v : W} (h : 𝒯.Reachable u v) : 𝒯.Path u v := by
  classical exact h.some.toPath

open scoped Classical in
/-- **Cycle of a group element in the quotient graph.** The signed edge counts (`walkCycle`)
of the chosen path from `v₀` to `g • v₀`, or zero if they are not reachable. The endpoints
`v₀` and `g • v₀` lie in one orbit, so the image of the path in the quotient graph is a closed
walk, which these counts record. -/
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

theorem dartIndex_eq_zero_of_smul_eq_symm (q : QuotEdge G 𝒯) {g : G} {d : 𝒯.Dart}
    (h : g • d = d.symm) : dartIndex 𝒯 q d = 0 := by
  rw [dartIndex, ← h, quotEdge_mk_smul, sub_self]

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
  rw [pathCycle, dite_eq_left p.1.reachable,
    (hac.subsingleton_path v₀ (g • v₀)).elim (somePath p.1.reachable) p]

theorem pathCycle_of_not_reachable (v₀ : W) (g : G) (h : ¬𝒯.Reachable v₀ (g • v₀)) :
    pathCycle 𝒯 orb v₀ g = 0 := by
  rw [pathCycle, dite_eq_right h]

end lemmas

end Mumford

end CerednikDrinfeld

end
