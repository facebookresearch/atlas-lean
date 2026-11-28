/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Rotate
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# Closed combinatorial surface meshes

A `Mesh V` is a list of polygonal faces, each a cyclic list of vertices. This file defines the
vertices, edges and Euler characteristic `chi` of a mesh, and decidable predicates for closed
surfaces (`ClosedSurface`: valid faces, every edge in exactly two faces, every vertex link a
single cycle), for consistent orientation, and for orientability.

`ConsistentlyOriented` and `Orientable` are edge-parity conditions on raw meshes.
`ConsistentlyOriented` tests the faces as listed: every directed edge is used by at most one face
and its reverse by some face. `Orientable` asks for some choice of face reversals that passes this
test, so a failed listed orientation is no obstruction: two copies of one triangle use the same
directed edges, yet reversing one copy orients them. For a mesh with `ClosedSurface` the two
predicates are the usual coherent orientation and orientability of the closed surface. On a raw
mesh `Orientable` fails exactly when some face has a directed edge `(a, b)` that no other face uses
in either direction, while `(b, a)` is absent from that face (`EdgesPaired` fails), or when no
flips meet the parity constraints between faces (`orientable_iff_edgesPaired_and_flipCompatible`).
One face may supply both directions of an edge, so the single face `[0, 1]` is `Orientable`.
`Valid` faces never do, so in a `Valid` orientable mesh every edge lies in a second face
(`Orientable.edge_shared_of_valid`): there a boundary edge rules orientability out.

`faceCount` and `linkDegree` count list entries. On raw input a face that traverses an edge twice
counts once in `faceCount`, and a loop `s(u, u)` in a vertex link counts once in `linkDegree`;
`Valid` faces produce neither.

## Main definitions

* `Mesh`, `vertices`, `edges`, `chi`: a mesh, its vertex and edge sets, and `V - E + F`.
* `ClosedSurface`, `ConsistentlyOriented`, `reorient`, `Orientable`.
* `orientationOf`: face flips computed by propagating parity constraints over the
  face-adjacency (dual) graph in polynomial time.

## Main results

* `orientable_iff_edgesPaired_and_flipCompatible`: orientability as parity constraints between
  faces sharing an edge.
* `orientable_iff_consistentlyOriented_orientationOf`: the algorithm decides orientability; this
  gives the `Decidable (Orientable M)` instance.
* `Orientable.edge_shared_of_valid`: a `Valid` orientable mesh has no boundary edge.

## Examples

* `tetra`, `cube`: the boundaries of a tetrahedron and a cube (`chi = 2`).
* `csaszar`: the seven-vertex triangulation of the torus (`chi = 0`), the combinatorial type of
  the Császár polyhedron.

## References

* Á. Császár, *A polyhedron without diagonals*, Acta Sci. Math. (Szeged) 13 (1949), 140–142.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Geometry.SurfaceMesh

/-- **Surface mesh.** A list of faces, each a list of vertices read cyclically: the face `f` has
the directed edges `(f[i], f[i + 1])`, with indices taken mod `f.length` (`directedEdgesOfFace`).
The faces are raw lists; `Valid` asks for polygons. -/
structure Mesh (V : Type _) where
  faces : List (List V)

def directedEdgesOfFace {V : Type _} (f : List V) :
    List (V × V) :=
  f.zip (f.rotate 1)

def allDirectedEdges {V : Type _} (M : Mesh V) :
    List (V × V) :=
  M.faces.flatMap directedEdgesOfFace

def edgesList {V : Type _} (M : Mesh V) : List (Sym2 V) :=
  (allDirectedEdges M).map (fun p => Sym2.mk p.1 p.2)

def verticesList {V : Type _} (M : Mesh V) : List V :=
  (allDirectedEdges M).flatMap (fun p => [p.1, p.2])

def vertices {V : Type _} [DecidableEq V] (M : Mesh V) : Finset V :=
  (verticesList M).toFinset

def edges {V : Type _} [DecidableEq V] (M : Mesh V) : Finset (Sym2 V) :=
  (edgesList M).toFinset

/-- **Euler characteristic.** `V - E + F`, with vertices and edges counted as sets and faces as
entries of `M.faces`. -/
def chi {V : Type _} [DecidableEq V] (M : Mesh V) : Int :=
  ((vertices M).card : Int) - ((edges M).card : Int) + (M.faces.length : Int)

/-- **Valid faces.** Every face has at least three vertices, all distinct, and no two faces are
cyclic rotations of each other, in the same or the opposite direction. -/
def Valid {V : Type _} (M : Mesh V) : Prop :=
  (∀ f ∈ M.faces, 3 ≤ f.length ∧ f.Nodup) ∧
    M.faces.Pairwise (fun f₁ f₂ =>
      ¬ List.IsRotated f₁ f₂ ∧ ¬ List.IsRotated f₁.reverse f₂)

/-- **Faces at an edge.** The number of entries of `M.faces` that traverse the undirected edge
`e`. A face that traverses `e` more than once, which only a face with a repeated vertex or fewer
than three vertices can do, counts once. -/
def faceCount {V : Type _} [DecidableEq V] (M : Mesh V) (e : Sym2 V) :
    Nat :=
  (M.faces.filter (fun f => decide (e ∈ (directedEdgesOfFace f).map
    (fun p => Sym2.mk p.1 p.2)))).length

/-- **Edge manifold.** Every edge of the mesh lies in exactly two faces, as `faceCount` counts
them. -/
def EdgeManifold {V : Type _} [DecidableEq V] (M : Mesh V) : Prop :=
  ∀ e ∈ edgesList M, faceCount M e = 2

def linkPairsOfFace {V : Type _} [DecidableEq V] (f : List V) (v : V) :
    List (Sym2 V) :=
  ((f.zip (f.rotate 1)).zip (f.rotate 2)).filterMap
    (fun ((a, x), b) => if x = v then some (Sym2.mk a b) else none)

def linkEdgesList {V : Type _} [DecidableEq V] (M : Mesh V) (v : V) :
    List (Sym2 V) :=
  M.faces.flatMap (fun f => linkPairsOfFace f v)

def linkEdges {V : Type _} [DecidableEq V] (M : Mesh V) (v : V) :
    Finset (Sym2 V) :=
  (linkEdgesList M v).toFinset

def linkVertsList {V : Type _} [DecidableEq V] (M : Mesh V) (v : V) :
    List V :=
  (allDirectedEdges M).filterMap (fun p =>
    if p.1 = v then some p.2 else if p.2 = v then some p.1 else none)

def linkVerts {V : Type _} [DecidableEq V] (M : Mesh V) (v : V) :
    Finset V :=
  (linkVertsList M v).toFinset

/-- **Link degree.** The number of entries of `linkEdgesList M v` that contain `u`. Each corner
of a face at `v` contributes one entry, the edge joining the corner's two neighbors, so a loop
`s(u, u)`, which only a face with a repeated vertex or fewer than three vertices produces, counts
once rather than twice. `Valid` faces produce no loops, so on the meshes `ClosedSurface` accepts
this is the degree of `u` in the link of `v`, counted with multiplicity. -/
def linkDegree {V : Type _} [DecidableEq V] (M : Mesh V) (v u : V) :
    Nat :=
  ((linkEdgesList M v).filter (fun e => decide (u ∈ e))).length

def neighborsFinset {V : Type _} [DecidableEq V] (M : Mesh V) (v u : V) :
    Finset V :=
  (linkVerts M v).filter (fun w => w ≠ u ∧ Sym2.mk u w ∈ linkEdges M v)

def expandFinset {V : Type _} [DecidableEq V] (M : Mesh V) (v : V)
    (S : Finset V) : Finset V :=
  S ∪ S.biUnion (neighborsFinset M v)

def closureFinset {V : Type _} [DecidableEq V] (M : Mesh V) (v : V) :
    Nat → Finset V → Finset V
  | 0, S => S
  | n + 1, S => closureFinset M v n (expandFinset M v S)

def LinkConnected {V : Type _} [DecidableEq V] (M : Mesh V) (v : V) :
    Prop :=
  ∃ r ∈ linkVertsList M v,
    (closureFinset M v (linkVerts M v).card {r} = linkVerts M v)

/-- **Vertex links are cycles.** At every vertex `v`, each vertex `u` joined to `v` by an edge has
degree `2` in the link of `v` (`linkDegree`), and the link of `v` is connected (`LinkConnected`).
On `Valid` faces this says that every vertex link is a single cycle. -/
def VertexLinkCycle {V : Type _} [DecidableEq V] (M : Mesh V) : Prop :=
  ∀ v ∈ verticesList M,
    (∀ u ∈ linkVertsList M v, linkDegree M v u = 2) ∧ LinkConnected M v

/-- **Closed surface.** `Valid` faces, every edge in exactly two faces (`EdgeManifold`), and every
vertex link a single cycle (`VertexLinkCycle`): the faces form a closed surface, not necessarily
connected. -/
def ClosedSurface {V : Type _} [DecidableEq V] (M : Mesh V) : Prop :=
  Valid M ∧ EdgeManifold M ∧ VertexLinkCycle M

/-- **Consistent orientation.** The faces as listed are consistently oriented: every directed edge
is used by at most one face, and its reverse by some face. For a mesh with `ClosedSurface` this says
the faces are coherently oriented: the two faces at each edge traverse it in opposite directions.
On a raw mesh it is only this test of the listed orientation, which fails when two faces use the
same directed edge or a face uses a directed edge whose reverse no face uses; reversing faces may
repair either failure (`Orientable`). The faces need not be valid polygons, and one face may supply
both directions of an edge. -/
def ConsistentlyOriented {V : Type _} [DecidableEq V] (M : Mesh V) :
    Prop :=
  (∀ d ∈ allDirectedEdges M,
    (M.faces.filter (fun f => decide (d ∈ directedEdgesOfFace f))).length ≤ 1) ∧
  (∀ d ∈ allDirectedEdges M, (d.2, d.1) ∈ allDirectedEdges M)

/-- **Reorientation.** Reverse the faces whose `flip` is `true`. -/
def reorient {V : Type _} (M : Mesh V)
    (flip : Fin M.faces.length → Bool) : Mesh V :=
  ⟨List.ofFn (fun i => if flip i then M.faces[i].reverse else M.faces[i])⟩

/-- **Orientability.** Some choice of face reversals makes the mesh `ConsistentlyOriented`. For a
mesh with `ClosedSurface` this is orientability of the closed surface it describes. On a raw mesh it
is only the edge-parity condition, and a failed listed orientation is no obstruction: two copies of
one triangle use the same directed edges, yet reversing one copy gives each direction once.
Orientability fails exactly when some face has a directed edge `(a, b)` that no other face uses in
either direction, while `(b, a)` is absent from that face (`EdgesPaired` fails), or when no flips
meet the parity constraints between faces (`orientable_iff_edgesPaired_and_flipCompatible`). One
face may supply both directions of an edge: the single face `[0, 1]` is orientable. `Valid` faces
never do, so in a `Valid` orientable mesh every edge lies in a second face
(`Orientable.edge_shared_of_valid`), and a boundary edge rules orientability out. -/
def Orientable {V : Type _} [DecidableEq V] (M : Mesh V) : Prop :=
  ∃ flip : Fin M.faces.length → Bool, ConsistentlyOriented (reorient M flip)

instance Valid.decidable {V : Type _} [DecidableEq V] (M : Mesh V) :
    Decidable (Valid M) := by
  unfold Valid
  infer_instance

instance EdgeManifold.decidable {V : Type _} [DecidableEq V] (M : Mesh V) :
    Decidable (EdgeManifold M) := by
  unfold EdgeManifold
  infer_instance

instance LinkConnected.decidable {V : Type _} [DecidableEq V] (M : Mesh V)
    (v : V) : Decidable (LinkConnected M v) := by
  unfold LinkConnected
  infer_instance

instance VertexLinkCycle.decidable {V : Type _} [DecidableEq V]
    (M : Mesh V) : Decidable (VertexLinkCycle M) := by
  unfold VertexLinkCycle
  infer_instance

instance ClosedSurface.decidable {V : Type _} [DecidableEq V] (M : Mesh V) :
    Decidable (ClosedSurface M) := by
  unfold ClosedSurface
  infer_instance

instance ConsistentlyOriented.decidable {V : Type _} [DecidableEq V]
    (M : Mesh V) : Decidable (ConsistentlyOriented M) := by
  unfold ConsistentlyOriented
  infer_instance

/-! ### Orientation constraints between faces -/

section OrientationLemmas

variable {V : Type _}

theorem mem_directedEdgesOfFace {f : List V} {a b : V} :
    (a, b) ∈ directedEdgesOfFace f ↔
      ∃ (i : ℕ) (h : i < f.length),
        f[i] = a ∧ f[(i + 1) % f.length]'(Nat.mod_lt _ (by omega)) = b := by
  unfold directedEdgesOfFace
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, he⟩
    simp only [List.length_zip, List.length_rotate, Nat.min_self] at hi
    rw [List.getElem_zip, List.getElem_rotate, Prod.mk.injEq] at he
    exact ⟨i, hi, he.1, he.2⟩
  · rintro ⟨i, hi, ha, hb⟩
    refine ⟨i, by simpa using hi, ?_⟩
    rw [List.getElem_zip, List.getElem_rotate, ha, hb]

private theorem succ_mod_reflect {n i : ℕ} (hi : i < n) :
    (n - 1 - (i + 1) % n + 1) % n = n - 1 - i := by
  rcases Nat.lt_or_ge (i + 1) n with h | h
  · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show i + 1 = n by omega, Nat.mod_self, Nat.sub_zero, Nat.sub_add_cancel (by omega),
      Nat.mod_self]
    omega

/-- **Reversed face.** Reversing a face reverses each of its directed edges. -/
theorem mem_directedEdgesOfFace_reverse {f : List V} {a b : V} :
    (a, b) ∈ directedEdgesOfFace f.reverse ↔ (b, a) ∈ directedEdgesOfFace f := by
  rw [mem_directedEdgesOfFace, mem_directedEdgesOfFace]
  simp only [List.length_reverse, List.getElem_reverse]
  constructor
  · rintro ⟨i, hi, ha, hb⟩
    refine ⟨f.length - 1 - (i + 1) % f.length, by omega, hb, ?_⟩
    rw [← ha]
    congr 1
    exact succ_mod_reflect hi
  · rintro ⟨k, hk, hb, ha⟩
    have hlt : (k + 1) % f.length < f.length := Nat.mod_lt _ (by omega)
    refine ⟨f.length - 1 - (k + 1) % f.length, by omega, ?_, ?_⟩
    · rw [← ha]
      congr 1
      omega
    · rw [← hb]
      congr 1
      rw [succ_mod_reflect hk]
      omega

/-- **Valid faces use one direction per edge.** Only a face with a repeated vertex or fewer than
three vertices can traverse an edge in both directions. -/
theorem swap_notMem_directedEdgesOfFace_of_nodup {f : List V} (hnd : f.Nodup)
    (hlen : 3 ≤ f.length) {a b : V} (h : (a, b) ∈ directedEdgesOfFace f) :
    (b, a) ∉ directedEdgesOfFace f := by
  intro h'
  obtain ⟨i, hi, hia, hib⟩ := mem_directedEdgesOfFace.mp h
  obtain ⟨k, hk, hkb, hka⟩ := mem_directedEdgesOfFace.mp h'
  have h1 : k = (i + 1) % f.length := hnd.getElem_inj_iff.mp (hkb.trans hib.symm)
  have h2 : (k + 1) % f.length = i := hnd.getElem_inj_iff.mp (hka.trans hia.symm)
  subst h1
  rcases Nat.lt_or_ge (i + 1) f.length with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h2
    rcases Nat.lt_or_ge (i + 1 + 1) f.length with hlt2 | hge2
    · rw [Nat.mod_eq_of_lt hlt2] at h2
      omega
    · rw [show i + 1 + 1 = f.length by omega, Nat.mod_self] at h2
      omega
  · rw [show i + 1 = f.length by omega, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega)] at h2
    omega

private theorem mem_reoriented_of_false {M : Mesh V} {flip : Fin M.faces.length → Bool}
    {i : Fin M.faces.length} (h : flip i = false) {a b : V} :
    (a, b) ∈ directedEdgesOfFace (if flip i then M.faces[i].reverse else M.faces[i]) ↔
      (a, b) ∈ directedEdgesOfFace M.faces[i] := by
  simp [h]

private theorem mem_reoriented_of_true {M : Mesh V} {flip : Fin M.faces.length → Bool}
    {i : Fin M.faces.length} (h : flip i = true) {a b : V} :
    (a, b) ∈ directedEdgesOfFace (if flip i then M.faces[i].reverse else M.faces[i]) ↔
      (b, a) ∈ directedEdgesOfFace M.faces[i] := by
  simp [h, mem_directedEdgesOfFace_reverse]

end OrientationLemmas

section Orientation

variable {V : Type _} [DecidableEq V]

/-- **Shared edge in the same direction.** `sharesSameEdge f g` holds when the faces `f` and `g`
traverse some edge in the same direction; two such faces need opposite flips in a consistent
orientation. -/
def sharesSameEdge (f g : List V) : Bool :=
  (directedEdgesOfFace f).any fun e => decide (e ∈ directedEdgesOfFace g)

/-- **Shared edge in opposite directions.** `sharesOppositeEdge f g` holds when the faces `f` and
`g` traverse some edge in opposite directions; two such faces need equal flips in a consistent
orientation. -/
def sharesOppositeEdge (f g : List V) : Bool :=
  (directedEdgesOfFace f).any fun e => decide ((e.2, e.1) ∈ directedEdgesOfFace g)

theorem sharesSameEdge_iff {f g : List V} :
    sharesSameEdge f g = true ↔ ∃ a b, (a, b) ∈ directedEdgesOfFace f ∧
      (a, b) ∈ directedEdgesOfFace g := by
  simp [sharesSameEdge, List.any_eq_true]

theorem sharesOppositeEdge_iff {f g : List V} :
    sharesOppositeEdge f g = true ↔ ∃ a b, (a, b) ∈ directedEdgesOfFace f ∧
      (b, a) ∈ directedEdgesOfFace g := by
  simp [sharesOppositeEdge, List.any_eq_true]

theorem sharesSameEdge_comm {f g : List V} (h : sharesSameEdge f g = true) :
    sharesSameEdge g f = true := by
  obtain ⟨a, b, h₁, h₂⟩ := sharesSameEdge_iff.mp h
  exact sharesSameEdge_iff.mpr ⟨a, b, h₂, h₁⟩

theorem sharesOppositeEdge_comm {f g : List V} (h : sharesOppositeEdge f g = true) :
    sharesOppositeEdge g f = true := by
  obtain ⟨a, b, h₁, h₂⟩ := sharesOppositeEdge_iff.mp h
  exact sharesOppositeEdge_iff.mpr ⟨b, a, h₂, h₁⟩

/-- **Compatible flips.** A flip assignment is compatible when every pair of distinct faces
traversing a common edge in the same direction gets opposite flips, and every pair traversing a
common edge in opposite directions gets equal flips. These are parity constraints on the
face-adjacency (dual) graph. -/
def FlipCompatible (M : Mesh V) (flip : Fin M.faces.length → Bool) : Prop :=
  ∀ i j, i ≠ j →
    (sharesSameEdge M.faces[i] M.faces[j] = true → flip i ≠ flip j) ∧
      (sharesOppositeEdge M.faces[i] M.faces[j] = true → flip i = flip j)

/-- **Paired edges.** For every directed edge `(a, b)` of a face, either `(b, a)` is also a
directed edge of that face (possibly the same occurrence, when `a = b`), or another face uses the
edge in either direction. This is the part of `Orientable` that does not depend on the flips
(`orientable_iff_edgesPaired_and_flipCompatible`); it fails exactly when some face has a directed
edge `(a, b)` that no other face uses in either direction, while `(b, a)` is absent from that
face. -/
def EdgesPaired (M : Mesh V) : Prop :=
  ∀ (i : Fin M.faces.length), ∀ e ∈ directedEdgesOfFace M.faces[i],
    (e.2, e.1) ∈ directedEdgesOfFace M.faces[i] ∨
      ∃ j, j ≠ i ∧ (e ∈ directedEdgesOfFace M.faces[j] ∨
        (e.2, e.1) ∈ directedEdgesOfFace M.faces[j])

instance EdgesPaired.decidable (M : Mesh V) : Decidable (EdgesPaired M) := by
  unfold EdgesPaired
  infer_instance

private theorem length_filter_ofFn_le_one {α : Type _} {n : ℕ} (g : Fin n → α) (p : α → Bool) :
    ((List.ofFn g).filter p).length ≤ 1 ↔ ∀ i j, p (g i) = true → p (g j) = true → i = j := by
  classical
  rw [List.ofFn_eq_map, List.filter_map, List.length_map,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _), List.toFinset_filter,
    List.toFinset_finRange, Finset.card_le_one]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  exact ⟨fun h i j hi hj => h i hi j hj, fun h i hi j hj => h i j hi hj⟩

/-- **Consistent orientation by face index.** `ConsistentlyOriented` for a reoriented mesh,
stated with face indices. -/
theorem consistentlyOriented_reorient_iff (M : Mesh V) (flip : Fin M.faces.length → Bool) :
    ConsistentlyOriented (reorient M flip) ↔
      (∀ (a b : V) (i j : Fin M.faces.length),
        (a, b) ∈ directedEdgesOfFace (if flip i then M.faces[i].reverse else M.faces[i]) →
        (a, b) ∈ directedEdgesOfFace (if flip j then M.faces[j].reverse else M.faces[j]) →
        i = j) ∧
      (∀ (a b : V) (i : Fin M.faces.length),
        (a, b) ∈ directedEdgesOfFace (if flip i then M.faces[i].reverse else M.faces[i]) →
        ∃ j, (b, a) ∈ directedEdgesOfFace (if flip j then M.faces[j].reverse else M.faces[j])) := by
  have hall : ∀ d, d ∈ allDirectedEdges (reorient M flip) ↔ ∃ i : Fin M.faces.length,
      d ∈ directedEdgesOfFace (if flip i then M.faces[i].reverse else M.faces[i]) := by
    intro d
    simp only [allDirectedEdges, reorient, List.mem_flatMap, List.mem_ofFn]
    constructor
    · rintro ⟨f, ⟨i, rfl⟩, hd⟩
      exact ⟨i, hd⟩
    · rintro ⟨i, hd⟩
      exact ⟨_, ⟨i, rfl⟩, hd⟩
  unfold ConsistentlyOriented
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun a b i j hi hj => ?_, fun a b i hi => ?_⟩
    · have := h₁ (a, b) ((hall _).mpr ⟨i, hi⟩)
      simp only [reorient] at this
      exact (length_filter_ofFn_le_one _ _).mp this i j (by simpa using hi) (by simpa using hj)
    · exact (hall _).mp (h₂ (a, b) ((hall _).mpr ⟨i, hi⟩))
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun d hd => ?_, fun d hd => ?_⟩
    · simp only [reorient]
      refine (length_filter_ofFn_le_one _ _).mpr fun i j hi hj => ?_
      exact h₁ d.1 d.2 i j (by simpa using hi) (by simpa using hj)
    · obtain ⟨i, hi⟩ := (hall d).mp hd
      exact (hall _).mpr (h₂ d.1 d.2 i hi)

/-- **Compatible flips orient the mesh.** Edge pairing and the parity constraints give a
consistent orientation. -/
theorem consistentlyOriented_reorient_of_flipCompatible {M : Mesh V} (hpair : EdgesPaired M)
    {s : Fin M.faces.length → Bool} (hs : FlipCompatible M s) :
    ConsistentlyOriented (reorient M s) := by
  refine (consistentlyOriented_reorient_iff M s).mpr ⟨fun a b i j hi hj => ?_, fun a b i hi => ?_⟩
  · by_contra hij
    obtain ⟨hsame, hopp⟩ := hs i j hij
    cases hsi : s i <;> cases hsj : s j
    · rw [mem_reoriented_of_false hsi] at hi
      rw [mem_reoriented_of_false hsj] at hj
      exact hsame (sharesSameEdge_iff.mpr ⟨a, b, hi, hj⟩) (hsi.trans hsj.symm)
    · rw [mem_reoriented_of_false hsi] at hi
      rw [mem_reoriented_of_true hsj] at hj
      exact Bool.false_ne_true (hsi.symm.trans
        ((hopp (sharesOppositeEdge_iff.mpr ⟨a, b, hi, hj⟩)).trans hsj))
    · rw [mem_reoriented_of_true hsi] at hi
      rw [mem_reoriented_of_false hsj] at hj
      exact Bool.false_ne_true (hsj.symm.trans
        ((hopp (sharesOppositeEdge_iff.mpr ⟨b, a, hi, hj⟩)).symm.trans hsi))
    · rw [mem_reoriented_of_true hsi] at hi
      rw [mem_reoriented_of_true hsj] at hj
      exact hsame (sharesSameEdge_iff.mpr ⟨b, a, hi, hj⟩) (hsi.trans hsj.symm)
  · cases hsi : s i
    · rw [mem_reoriented_of_false hsi] at hi
      rcases hpair i (a, b) hi with hrev | ⟨j, hji, hj | hj⟩
      · exact ⟨i, (mem_reoriented_of_false hsi).mpr hrev⟩
      · have hne := (hs i j hji.symm).1 (sharesSameEdge_iff.mpr ⟨a, b, hi, hj⟩)
        cases hsj : s j
        · exact absurd (hsi.trans hsj.symm) hne
        · exact ⟨j, (mem_reoriented_of_true hsj).mpr hj⟩
      · have heq := (hs i j hji.symm).2 (sharesOppositeEdge_iff.mpr ⟨a, b, hi, hj⟩)
        exact ⟨j, (mem_reoriented_of_false (heq.symm.trans hsi)).mpr hj⟩
    · rw [mem_reoriented_of_true hsi] at hi
      rcases hpair i (b, a) hi with hrev | ⟨j, hji, hj | hj⟩
      · exact ⟨i, (mem_reoriented_of_true hsi).mpr hrev⟩
      · have hne := (hs i j hji.symm).1 (sharesSameEdge_iff.mpr ⟨b, a, hi, hj⟩)
        cases hsj : s j
        · exact ⟨j, (mem_reoriented_of_false hsj).mpr hj⟩
        · exact absurd (hsi.trans hsj.symm) hne
      · have heq := (hs i j hji.symm).2 (sharesOppositeEdge_iff.mpr ⟨b, a, hi, hj⟩)
        exact ⟨j, (mem_reoriented_of_true (heq.symm.trans hsi)).mpr hj⟩

/-- **Orientability as parity constraints.** A mesh is orientable exactly when its edges are
paired (`EdgesPaired`) and some flip assignment satisfies the parity constraints of
`FlipCompatible`. -/
theorem orientable_iff_edgesPaired_and_flipCompatible (M : Mesh V) :
    Orientable M ↔ EdgesPaired M ∧ ∃ flip, FlipCompatible M flip := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨h₁, h₂⟩ := (consistentlyOriented_reorient_iff M s).mp hs
    refine ⟨fun i ⟨a, b⟩ hab => ?_, s, fun i j hij => ⟨fun hsame hEq => ?_, fun hopp => ?_⟩⟩
    · cases hsi : s i
      · obtain ⟨j, hj⟩ := h₂ a b i ((mem_reoriented_of_false hsi).mpr hab)
        by_cases hji : j = i
        · subst hji
          exact Or.inl ((mem_reoriented_of_false hsi).mp hj)
        · refine Or.inr ⟨j, hji, ?_⟩
          cases hsj : s j
          · exact Or.inr ((mem_reoriented_of_false hsj).mp hj)
          · exact Or.inl ((mem_reoriented_of_true hsj).mp hj)
      · obtain ⟨j, hj⟩ := h₂ b a i ((mem_reoriented_of_true hsi).mpr hab)
        by_cases hji : j = i
        · subst hji
          exact Or.inl ((mem_reoriented_of_true hsi).mp hj)
        · refine Or.inr ⟨j, hji, ?_⟩
          cases hsj : s j
          · exact Or.inl ((mem_reoriented_of_false hsj).mp hj)
          · exact Or.inr ((mem_reoriented_of_true hsj).mp hj)
    · obtain ⟨a, b, hi, hj⟩ := sharesSameEdge_iff.mp hsame
      apply hij
      cases hsi : s i
      · have hsj : s j = false := hEq.symm.trans hsi
        exact h₁ a b i j ((mem_reoriented_of_false hsi).mpr hi)
          ((mem_reoriented_of_false hsj).mpr hj)
      · have hsj : s j = true := hEq.symm.trans hsi
        exact h₁ b a i j ((mem_reoriented_of_true hsi).mpr hi)
          ((mem_reoriented_of_true hsj).mpr hj)
    · obtain ⟨a, b, hi, hj⟩ := sharesOppositeEdge_iff.mp hopp
      cases hsi : s i <;> cases hsj : s j
      · rfl
      · exact absurd (h₁ a b i j ((mem_reoriented_of_false hsi).mpr hi)
          ((mem_reoriented_of_true hsj).mpr hj)) hij
      · exact absurd (h₁ b a i j ((mem_reoriented_of_true hsi).mpr hi)
          ((mem_reoriented_of_false hsj).mpr hj)) hij
      · rfl
  · rintro ⟨hpair, s, hs⟩
    exact ⟨s, consistentlyOriented_reorient_of_flipCompatible hpair hs⟩

/-- **No boundary edges in a valid orientable mesh.** In a `Valid` orientable mesh, every directed
edge of a face is traversed, in one direction or the other, by another face. -/
theorem Orientable.edge_shared_of_valid {M : Mesh V} (hO : Orientable M) (hV : Valid M)
    {i : Fin M.faces.length} {a b : V} (h : (a, b) ∈ directedEdgesOfFace M.faces[i]) :
    ∃ j, j ≠ i ∧ ((a, b) ∈ directedEdgesOfFace M.faces[j] ∨
      (b, a) ∈ directedEdgesOfFace M.faces[j]) := by
  have hface := hV.1 _ (List.getElem_mem i.isLt)
  rcases ((orientable_iff_edgesPaired_and_flipCompatible M).mp hO).1 i (a, b) h with hrev | hj
  · exact absurd hrev (swap_notMem_directedEdgesOfFace_of_nodup hface.2 hface.1 h)
  · exact hj

/-! ### A polynomial orientation algorithm

The algorithm grows a partial flip assignment on the face-adjacency (dual) graph. Each step
either assigns every unassigned face that has an assigned neighbor, reading the neighbor's
flip through the parity constraint (one breadth-first layer), or, when no such face exists,
starts a new component by assigning the first unassigned face `false`. While some face is
unassigned, each step assigns at least one, so `M.faces.length` steps assign every face. The
neighbor lists are computed once, in `O(F² L²)` time for `F` faces of length at most `L`, and each
step costs `O(F + C)` for `C` constraints. -/

/-- **Parity constraints at a face.** The constraints at face `j`: for each face `i ≠ j`,
`(i, true)` when faces `i` and `j` share an edge in the same direction, and `(i, false)` when they
share one in opposite directions. -/
def faceConstraints (M : Mesh V) (j : Fin M.faces.length) : List (Fin M.faces.length × Bool) :=
  let fs := M.faces.toArray
  (List.finRange M.faces.length).flatMap fun i =>
    if i = j then []
    else (if sharesSameEdge (fs.getD i []) (fs.getD j []) then [(i, true)] else []) ++
      (if sharesOppositeEdge (fs.getD i []) (fs.getD j []) then [(i, false)] else [])

omit [DecidableEq V] in
private theorem faces_toArray_getD (M : Mesh V) (i : Fin M.faces.length) :
    M.faces.toArray.getD i [] = M.faces[i] := by
  simp [Array.getD, i.isLt]

theorem mem_faceConstraints {M : Mesh V} {i j : Fin M.faces.length} {b : Bool} :
    (i, b) ∈ faceConstraints M j ↔ i ≠ j ∧
      (if b then sharesSameEdge M.faces[i] M.faces[j] else
        sharesOppositeEdge M.faces[i] M.faces[j]) = true := by
  simp only [faceConstraints, faces_toArray_getD, List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨k, hk⟩
    by_cases hkj : k = j
    · simp [hkj] at hk
    · simp only [hkj, ↓reduceIte, List.mem_append] at hk
      rcases hk with hk | hk
      · split_ifs at hk with hsame
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hk)
          exact ⟨hkj, by simpa using hsame⟩
        · simp at hk
      · split_ifs at hk with hopp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hk)
          exact ⟨hkj, by simpa using hopp⟩
        · simp at hk
  · rintro ⟨hij, hb⟩
    refine ⟨i, ?_⟩
    simp only [hij, ↓reduceIte, List.mem_append]
    cases b <;> simp_all

/-- **Constraint table.** The constraint lists of all faces, computed once. -/
def faceConstraintTable (M : Mesh V) : Array (List (Fin M.faces.length × Bool)) :=
  (List.ofFn (faceConstraints M)).toArray

/-- **Stored flip.** The flip of face `j` stored in a partial assignment. -/
def readFlip {n : ℕ} (arr : Array (Option Bool)) (j : Fin n) : Option Bool :=
  arr.getD j none

/-- **Forced flip.** The flip forced on face `j` by the first entry of its constraint list whose
face is assigned, if any. -/
def pullFlip {n : ℕ} (table : Array (List (Fin n × Bool))) (a : Fin n → Option Bool)
    (j : Fin n) : Option Bool :=
  (table.getD j []).findSome? fun p => (a p.1).map (xor p.2)

/-- **Propagation step.** One step of the algorithm on a partial assignment `a`. -/
def flipStepFun {n : ℕ} (table : Array (List (Fin n × Bool))) (a : Fin n → Option Bool) :
    Fin n → Option Bool :=
  let grow := (List.finRange n).any fun j => (a j).isNone && (pullFlip table a j).isSome
  let root := (List.finRange n).find? fun j => (a j).isNone
  fun j => if grow then (a j).or (pullFlip table a j) else if root = some j then some false else a j

/-- **Propagation step on arrays.** One step of the algorithm, storing the new partial assignment
in an array. It computes the same assignment as `flipStepFun`, testing the growth condition
once. -/
def flipStep {n : ℕ} (table : Array (List (Fin n × Bool))) (arr : Array (Option Bool)) :
    Array (Option Bool) :=
  let a : Fin n → Option Bool := readFlip arr
  if (List.finRange n).any fun j => (a j).isNone && (pullFlip table a j).isSome then
    (List.ofFn fun j => (a j).or (pullFlip table a j)).toArray
  else
    match (List.finRange n).find? fun j => (a j).isNone with
    | some k => (List.ofFn fun j => if k = j then some false else a j).toArray
    | none => (List.ofFn a).toArray

/-- **Final assignment.** The partial assignment after `M.faces.length` steps; every entry is
assigned. -/
def orientationArray (M : Mesh V) : Array (Option Bool) :=
  (flipStep (faceConstraintTable M))^[M.faces.length] #[]

/-- **Computed orientation.** The flips computed by the algorithm. When `M` is orientable,
`reorient M (orientationOf M)` is consistently oriented
(`orientable_iff_consistentlyOriented_orientationOf`). -/
def orientationOf (M : Mesh V) : Fin M.faces.length → Bool :=
  fun j => (readFlip (orientationArray M) j).getD false

private theorem getD_ofFn_toArray {α : Type _} {n : ℕ} (g : Fin n → α) (j : Fin n) (x : α) :
    (List.ofFn g).toArray.getD j x = g j := by
  simp [Array.getD, j.isLt]

private theorem readFlip_flipStep {n : ℕ} (table : Array (List (Fin n × Bool)))
    (arr : Array (Option Bool)) :
    readFlip (flipStep table arr) = flipStepFun table (readFlip arr) := by
  funext j
  dsimp only [flipStep, flipStepFun]
  by_cases hgrow : ((List.finRange n).any fun j =>
      (readFlip arr j).isNone && (pullFlip table (readFlip arr) j).isSome) = true
  · simp only [hgrow, ↓reduceIte]
    exact getD_ofFn_toArray _ _ _
  · simp only [hgrow, Bool.false_eq_true, ↓reduceIte]
    cases (List.finRange n).find? fun j => (readFlip arr j).isNone with
    | some k => exact (getD_ofFn_toArray _ j none).trans (by simp only [Option.some.injEq])
    | none => exact (getD_ofFn_toArray _ j none).trans (by simp)

private theorem readFlip_iterate {n : ℕ} (table : Array (List (Fin n × Bool))) (t : ℕ) :
    readFlip ((flipStep table)^[t] #[]) = (flipStepFun table)^[t] (fun _ => none) := by
  induction t with
  | zero => funext j; simp [readFlip]
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', readFlip_flipStep, ih]

private theorem faceConstraintTable_getD (M : Mesh V) (j : Fin M.faces.length) :
    (faceConstraintTable M).getD j [] = faceConstraints M j :=
  getD_ofFn_toArray _ _ _

/-- **Extendable assignments.** Partial assignments that extend to a compatible flip assignment.
-/
private def Extends (M : Mesh V) (a : Fin M.faces.length → Option Bool) : Prop :=
  ∃ s, FlipCompatible M s ∧ ∀ j b, a j = some b → s j = b

private theorem FlipCompatible.eq_xor {M : Mesh V} {s : Fin M.faces.length → Bool}
    (hs : FlipCompatible M s) {i j : Fin M.faces.length} {b : Bool}
    (h : (i, b) ∈ faceConstraints M j) : s j = xor b (s i) := by
  obtain ⟨hij, hb⟩ := mem_faceConstraints.mp h
  obtain ⟨hsame, hopp⟩ := hs i j hij
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hb
    simp [hopp hb]
  · simp only [↓reduceIte] at hb
    have key : ∀ x y : Bool, x ≠ y → y = xor true x := by decide
    exact key _ _ (hsame hb)

private theorem pullFlip_spec {M : Mesh V} {a : Fin M.faces.length → Option Bool}
    {j : Fin M.faces.length} {c : Bool}
    (h : pullFlip (faceConstraintTable M) a j = some c) :
    ∃ i b d, (i, b) ∈ faceConstraints M j ∧ a i = some d ∧ c = xor b d := by
  unfold pullFlip at h
  rw [faceConstraintTable_getD] at h
  obtain ⟨⟨i, b⟩, hmem, hp⟩ := List.exists_of_findSome?_eq_some h
  cases hai : a i with
  | none => simp [hai] at hp
  | some d =>
    simp only [hai, Option.map_some, Option.some.injEq] at hp
    exact ⟨i, b, d, hmem, hai, hp.symm⟩

private theorem pullFlip_eq_none {M : Mesh V} {a : Fin M.faces.length → Option Bool}
    {j : Fin M.faces.length} (h : pullFlip (faceConstraintTable M) a j = none)
    {i : Fin M.faces.length} {b : Bool} (hmem : (i, b) ∈ faceConstraints M j) : a i = none := by
  unfold pullFlip at h
  rw [faceConstraintTable_getD, List.findSome?_eq_none_iff] at h
  have := h (i, b) hmem
  cases hai : a i <;> simp_all

private theorem extends_flipStepFun {M : Mesh V} {a : Fin M.faces.length → Option Bool}
    (ha : Extends M a) : Extends M (flipStepFun (faceConstraintTable M) a) := by
  obtain ⟨s, hs, hsa⟩ := ha
  unfold flipStepFun
  simp only
  split_ifs with hgrow
  · refine ⟨s, hs, fun j b hj => ?_⟩
    cases haj : a j with
    | some d => simp only [haj, Option.some_or, Option.some.injEq] at hj; exact hj ▸ hsa j d haj
    | none =>
      simp only [haj, Option.none_or] at hj
      obtain ⟨i, c, d, hmem, hai, rfl⟩ := pullFlip_spec hj
      rw [hs.eq_xor hmem, hsa i d hai]
  · -- no unassigned face has an assigned neighbor
    have hclosed : ∀ j, a j = none → pullFlip (faceConstraintTable M) a j = none := by
      intro j hj
      by_contra hne
      apply hgrow
      rw [List.any_eq_true]
      exact ⟨j, List.mem_finRange _, by simp [hj, Option.ne_none_iff_isSome.mp hne]⟩
    cases hroot : (List.finRange M.faces.length).find? fun j => (a j).isNone with
    | none => exact ⟨s, hs, fun j b hj => by simpa [hroot] using hsa j b (by simpa using hj)⟩
    | some k =>
      have hk : a k = none := by simpa using List.find?_some hroot
      -- flip every unassigned face relative to `s` so that `k` gets `false`
      let s' : Fin M.faces.length → Bool := fun j => if a j = none then xor (s j) (s k) else s j
      have hcross : ∀ i j, a i ≠ none → a j = none → i ≠ j →
          sharesSameEdge M.faces[i] M.faces[j] = false ∧
            sharesOppositeEdge M.faces[i] M.faces[j] = false := by
        intro i j hi hj hij
        constructor
        · by_contra h
          exact hi (pullFlip_eq_none (hclosed j hj)
            ((mem_faceConstraints (b := true)).mpr ⟨hij, by simpa using h⟩))
        · by_contra h
          exact hi (pullFlip_eq_none (hclosed j hj)
            ((mem_faceConstraints (b := false)).mpr ⟨hij, by simpa using h⟩))
      refine ⟨s', fun i j hij => ⟨fun hsame => ?_, fun hopp => ?_⟩, fun j b hj => ?_⟩
      · have := (hs i j hij).1 hsame
        by_cases hi : a i = none <;> by_cases hj : a j = none
        · simp only [s', hi, hj, ↓reduceIte]
          have key : ∀ x y z : Bool, x ≠ y → xor x z ≠ xor y z := by decide
          exact key _ _ _ this
        · exact absurd ((hcross j i hj hi (Ne.symm hij)).1.symm.trans (sharesSameEdge_comm hsame))
            Bool.false_ne_true
        · exact absurd ((hcross i j hi hj hij).1.symm.trans hsame) Bool.false_ne_true
        · simpa [s', hi, hj] using this
      · have := (hs i j hij).2 hopp
        by_cases hi : a i = none <;> by_cases hj : a j = none
        · simp [s', hi, hj, this]
        · exact absurd ((hcross j i hj hi (Ne.symm hij)).2.symm.trans
            (sharesOppositeEdge_comm hopp)) Bool.false_ne_true
        · exact absurd ((hcross i j hi hj hij).2.symm.trans hopp) Bool.false_ne_true
        · simpa [s', hi, hj] using this
      · by_cases hjk : j = k
        · subst hjk
          simp only [↓reduceIte, Option.some.injEq] at hj
          simp [s', hk, ← hj]
        · have hroot' : (some k = some j) = False := by simp [Ne.symm hjk]
          simp only [hroot', ↓reduceIte] at hj
          simp [s', hj, hsa j b hj]

private theorem flipStepFun_isSome {n : ℕ} (table : Array (List (Fin n × Bool)))
    (a : Fin n → Option Bool) {j : Fin n} (h : (a j).isSome) :
    (flipStepFun table a j).isSome := by
  unfold flipStepFun
  split_ifs with hgrow hroot
  · cases haj : a j <;> simp_all
  · simp
  · exact h

private theorem flipStepFun_progress {n : ℕ} (table : Array (List (Fin n × Bool)))
    (a : Fin n → Option Bool) (h : ∃ j, a j = none) :
    ∃ j, a j = none ∧ (flipStepFun table a j).isSome := by
  unfold flipStepFun
  by_cases hgrow : (List.finRange n).any fun j => (a j).isNone && (pullFlip table a j).isSome
  · obtain ⟨j, -, hj⟩ := List.any_eq_true.mp hgrow
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hj
    exact ⟨j, hj.1, by simp [hgrow, hj.1, hj.2]⟩
  · obtain ⟨j, hj⟩ := h
    cases hroot : (List.finRange n).find? fun j => (a j).isNone with
    | none =>
      exact absurd (List.find?_eq_none.mp hroot j (List.mem_finRange _)) (by simp [hj])
    | some k =>
      exact ⟨k, by simpa using List.find?_some hroot, by simp [hgrow]⟩

private theorem card_assigned_iterate {n : ℕ} (table : Array (List (Fin n × Bool))) (t : ℕ) :
    min t n ≤
      (Finset.univ.filter fun j => ((flipStepFun table)^[t] (fun _ => none) j).isSome).card := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    set a := (flipStepFun table)^[t] (fun _ => none)
    have hsub : (Finset.univ.filter fun j => (a j).isSome) ⊆
        Finset.univ.filter fun j => (flipStepFun table a j).isSome := by
      intro j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact flipStepFun_isSome table a
    by_cases hall : ∃ j, a j = none
    · obtain ⟨j, hj, hj'⟩ := flipStepFun_progress table a hall
      have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => by
        have : j ∈ Finset.univ.filter fun j => (flipStepFun table a j).isSome := by simp [hj']
        rw [← heq] at this
        simp [hj] at this⟩)
      omega
    · push Not at hall
      have : (Finset.univ.filter fun j => (a j).isSome) = Finset.univ := by
        ext j; simp [Option.isSome_iff_ne_none, hall j]
      have hcard := Finset.card_le_card hsub
      rw [this, Finset.card_univ, Fintype.card_fin] at hcard
      omega

private theorem orientationArray_isSome (M : Mesh V) (j : Fin M.faces.length) :
    (readFlip (orientationArray M) j).isSome := by
  unfold orientationArray
  rw [readFlip_iterate]
  have h := card_assigned_iterate (faceConstraintTable M) M.faces.length
  rw [min_self] at h
  by_contra hj
  have hlt := Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨j, Finset.mem_univ _, hj⟩ :
    (Finset.univ.filter fun j =>
      ((flipStepFun (faceConstraintTable M))^[M.faces.length] (fun _ => none) j).isSome) ⊂
      Finset.univ)
  rw [Finset.card_univ, Fintype.card_fin] at hlt
  omega

/-- **Completeness of the algorithm.** If some flip assignment is compatible, so is the one the
algorithm computes. -/
theorem flipCompatible_orientationOf {M : Mesh V} (h : ∃ s, FlipCompatible M s) :
    FlipCompatible M (orientationOf M) := by
  have hext : ∀ t, Extends M ((flipStepFun (faceConstraintTable M))^[t] fun _ => none) := by
    intro t
    induction t with
    | zero =>
      obtain ⟨s, hs⟩ := h
      exact ⟨s, hs, fun j b hj => by simp at hj⟩
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact extends_flipStepFun ih
  obtain ⟨s, hs, hsa⟩ := hext M.faces.length
  have : orientationOf M = s := by
    funext j
    have hj := orientationArray_isSome M j
    unfold orientationArray at hj
    rw [readFlip_iterate] at hj
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hj
    simp only [orientationOf, orientationArray, readFlip_iterate, hb, Option.getD_some]
    exact (hsa j b hb).symm
  rw [this]
  exact hs

/-- **Correctness of the orientation algorithm.** A mesh is orientable exactly when the flips
computed by `orientationOf` orient it consistently. -/
theorem orientable_iff_consistentlyOriented_orientationOf (M : Mesh V) :
    Orientable M ↔ ConsistentlyOriented (reorient M (orientationOf M)) := by
  constructor
  · intro h
    obtain ⟨hpair, hflip⟩ := (orientable_iff_edgesPaired_and_flipCompatible M).mp h
    exact consistentlyOriented_reorient_of_flipCompatible hpair (flipCompatible_orientationOf hflip)
  · intro h
    exact ⟨orientationOf M, h⟩

/-- **Reorientation by a stored assignment.** `reorient` driven by a stored assignment, so that
compiled code computes the assignment once. -/
def reorientBy (M : Mesh V) (arr : Array (Option Bool)) : Mesh V :=
  reorient M fun j => (readFlip arr j).getD false

/-- **Deciding orientability.** Orientability is decided by the polynomial algorithm behind
`orientationOf`. -/
instance Orientable.decidable (M : Mesh V) : Decidable (Orientable M) :=
  decidable_of_iff (ConsistentlyOriented (reorientBy M (orientationArray M)))
    (orientable_iff_consistentlyOriented_orientationOf M).symm

end Orientation

def tetra : Mesh (Fin 4) :=
  ⟨[[0, 1, 2], [0, 3, 1], [0, 2, 3], [1, 3, 2]]⟩

def cube : Mesh (Fin 8) :=
  ⟨[[0, 1, 2, 3], [4, 7, 6, 5], [0, 4, 5, 1], [3, 2, 6, 7],
    [0, 3, 7, 4], [1, 5, 6, 2]]⟩

/-- **Császár torus.** The seven-vertex triangulation of the torus: the fourteen triangles
`[i, i + 1, i + 3]` and `[i, i + 3, i + 2]` for `i = 0, …, 6`, with vertex labels taken mod `7`.
This cyclic labeling is the standard description of the combinatorial type of the Császár polyhedron
(Császár, 1949), a torus whose `21` edges join every pair of its `7` vertices; Császár's coordinates
for a geometric realization are not used here. -/
def csaszar : Mesh (Fin 7) :=
  ⟨[[0, 1, 3], [0, 3, 2], [1, 2, 4], [1, 4, 3], [2, 3, 5], [2, 5, 4],
    [3, 4, 6], [3, 6, 5], [4, 5, 0], [4, 0, 6], [5, 6, 1], [5, 1, 0],
    [6, 0, 2], [6, 2, 1]]⟩

end Cslib.Algorithms.Lean.Geometry.SurfaceMesh
