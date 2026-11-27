/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Geometry.SurfaceMesh
public meta import CSLibExt.Algorithms.Lean.Geometry.SurfaceMesh
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic

namespace Cslib.Algorithms.Lean.Geometry.SurfaceMeshTests

open Cslib.Algorithms.Lean.Geometry.SurfaceMesh

def bowtie : Mesh (Fin 5) := ⟨[[0, 1, 2], [0, 3, 4]]⟩

/-- Three triangles on the edge `{0, 1}`: every link is connected, but the link of `0` is a star
whose center `1` has degree three. -/
def book : Mesh (Fin 5) := ⟨[[0, 1, 2], [0, 1, 3], [0, 1, 4]]⟩

/-- Two tetrahedral boundaries sharing only the vertex `0`: edges are paired and every link
vertex has degree two, but the link of `0` is two disjoint triangles. -/
def twoTetra : Mesh (Fin 7) :=
  ⟨[[0, 1, 2], [0, 3, 1], [0, 2, 3], [1, 3, 2], [0, 4, 5], [0, 6, 4], [0, 5, 6], [4, 6, 5]]⟩

def degenerate : Mesh (Fin 3) := ⟨[[0, 1, 1]]⟩

def subdivTetra : Mesh (Fin 5) :=
  ⟨[[0, 4, 1, 2], [0, 3, 1, 4], [0, 2, 3], [1, 3, 2]]⟩

/-- `tetra` with its first face listed in the opposite direction. -/
def tetraFlipped : Mesh (Fin 4) :=
  ⟨[[2, 1, 0], [0, 3, 1], [0, 2, 3], [1, 3, 2]]⟩

/-- The six-vertex triangulation of the real projective plane (the hemi-icosahedron). -/
def rp2 : Mesh (Fin 6) :=
  ⟨[[0, 1, 2], [0, 2, 3], [0, 3, 4], [0, 4, 5], [0, 5, 1], [1, 2, 4], [2, 3, 5], [3, 4, 1],
    [4, 5, 2], [5, 1, 3]]⟩

/-- A single triangle: its edges are not paired. -/
def disk : Mesh (Fin 3) := ⟨[[0, 1, 2]]⟩

/-- A single two-vertex face: not a valid polygon, but it uses both directions of its edge. -/
def digon : Mesh (Fin 2) := ⟨[[0, 1]]⟩

/-- A single one-vertex face: its only directed edge is the loop `(0, 0)`. -/
def monogon : Mesh (Fin 1) := ⟨[[0]]⟩

/-- Two copies of one triangle: as listed both use the same directed edges, but reversing one copy
orients them. -/
def twoCopies : Mesh (Fin 3) := ⟨[[0, 1, 2], [0, 1, 2]]⟩

/-- The raw face `[0, 1, 0]` repeats the vertex `0`, so its link at `1` is the loop `s(0, 0)`. -/
def rawLoop : Mesh (Fin 2) := ⟨[[0, 1, 0]]⟩

/-- The raw face `[0, 1, 0, 1]` traverses the edge `s(0, 1)` twice in each direction. -/
def rawRepeat : Mesh (Fin 2) := ⟨[[0, 1, 0, 1]]⟩

theorem tetra_vertices : (vertices tetra).card = 4 := by decide

theorem tetra_edges : (edges tetra).card = 6 := by decide

theorem tetra_faces_length : tetra.faces.length = 4 := by decide

theorem tetra_chi : chi tetra = 2 := by decide

theorem tetra_closed : ClosedSurface tetra := by decide

theorem tetra_oriented : ConsistentlyOriented tetra := by decide

theorem tetra_orientable : Orientable tetra := by decide

theorem cube_vertices : (vertices cube).card = 8 := by decide

theorem cube_edges : (edges cube).card = 12 := by decide

theorem cube_faces_length : cube.faces.length = 6 := by decide

theorem cube_chi : chi cube = 2 := by decide

theorem cube_closed : ClosedSurface cube := by decide

theorem cube_oriented : ConsistentlyOriented cube := by decide

theorem cube_orientable : Orientable cube := by decide

theorem csaszar_faces_cyclic :
    csaszar.faces = (List.finRange 7).flatMap fun i => [[i, i + 1, i + 3], [i, i + 3, i + 2]] := by
  decide

theorem csaszar_vertices : (vertices csaszar).card = 7 := by decide +kernel

theorem csaszar_edges : (edges csaszar).card = 21 := by decide +kernel

theorem csaszar_faces_length : csaszar.faces.length = 14 := by decide

theorem csaszar_chi : chi csaszar = 0 := by decide +kernel

theorem csaszar_closed : ClosedSurface csaszar := by decide +kernel

theorem csaszar_oriented : ConsistentlyOriented csaszar := by decide

theorem csaszar_orientable : Orientable csaszar := by decide +kernel

theorem bowtie_fails_link : ¬ VertexLinkCycle bowtie := by decide

/-- The bowtie fails the link condition through degrees: each link vertex at `0` has degree one. -/
theorem bowtie_link_degree_fails_at_zero :
    ¬ ∀ u ∈ linkVertsList bowtie 0, linkDegree bowtie 0 u = 2 := by decide

theorem book_links_connected : ∀ v ∈ verticesList book, LinkConnected book v := by decide

/-- With every link connected, only the degree condition fails. -/
theorem book_not_vertexLinkCycle : ¬ VertexLinkCycle book := by decide

theorem twoTetra_valid : Valid twoTetra := by decide

theorem twoTetra_edges_paired : EdgeManifold twoTetra := by decide

theorem twoTetra_link_degree_two :
    ∀ v ∈ verticesList twoTetra, ∀ u ∈ linkVertsList twoTetra v, linkDegree twoTetra v u = 2 := by
  decide

/-- With edges paired and every link degree two, only connectivity fails: the link of `0` is two
disjoint triangles. -/
theorem twoTetra_link_disconnected : ¬ LinkConnected twoTetra 0 := by decide

theorem twoTetra_not_closed : ¬ ClosedSurface twoTetra := by decide

/-- `Orientable` is the edge-parity condition, which this pinched mesh also meets. -/
theorem twoTetra_orientable : Orientable twoTetra := by decide

theorem degenerate_invalid : ¬ Valid degenerate := by decide

theorem subdivTetra_closed : ClosedSurface subdivTetra := by decide

theorem subdivTetra_oriented : ConsistentlyOriented subdivTetra := by decide

theorem subdivTetra_chi : chi subdivTetra = 2 := by decide

theorem tetraFlipped_closed : ClosedSurface tetraFlipped := by decide

theorem tetraFlipped_not_oriented : ¬ ConsistentlyOriented tetraFlipped := by decide

theorem tetraFlipped_reorient_first :
    ConsistentlyOriented (reorient tetraFlipped fun i => decide (i.val = 0)) := by decide

theorem tetraFlipped_reorient_none :
    ¬ ConsistentlyOriented (reorient tetraFlipped fun _ => false) := by decide

theorem tetraFlipped_orientable : Orientable tetraFlipped := by decide

theorem tetraFlipped_orientationOf :
    List.ofFn (orientationOf tetraFlipped) = [false, true, true, true] := by decide

theorem rp2_closed : ClosedSurface rp2 := by decide +kernel

theorem rp2_chi : chi rp2 = 1 := by decide +kernel

theorem rp2_not_orientable : ¬ Orientable rp2 := by decide +kernel

theorem rp2_not_flipCompatible : ¬ ∃ flip, FlipCompatible rp2 flip := fun h =>
  rp2_not_orientable ((orientable_iff_edgesPaired_and_flipCompatible rp2).mpr
    ⟨by decide +kernel, h⟩)

theorem disk_edges_unpaired : ¬ EdgesPaired disk := by decide

/-- A disk is not `Orientable` in the closed-edge sense, because its boundary edges are unpaired. -/
theorem disk_not_orientable_of_unpaired_edges : ¬ Orientable disk := fun h =>
  disk_edges_unpaired ((orientable_iff_edgesPaired_and_flipCompatible disk).mp h).1

/-- The edge-parity reading on a raw mesh: the invalid face `[0, 1]` passes, although its edge
lies in one face only. -/
theorem digon_orientable_not_valid : Orientable digon ∧ ¬ Valid digon := by decide

theorem digon_edge_in_one_face : faceCount digon s(0, 1) = 1 := by decide

/-- A face with fewer than three vertices produces a link loop without repeating a vertex: since
`[0, 1].rotate 2 = [0, 1]`, the corner of `digon` at `1` gives `s(0, 0)`. -/
theorem digon_linkEdgesList : linkEdgesList digon 1 = [s(0, 0)] := by decide

/-- Edge pairing is membership, not a second traversal: the loop `(0, 0)` occurs once in `[[0]]`
and is its own reverse, so `[[0]]` is `EdgesPaired` and, as listed, consistently oriented. -/
theorem monogon_edgesPaired :
    allDirectedEdges monogon = [(0, 0)] ∧ EdgesPaired monogon ∧ ConsistentlyOriented monogon := by
  decide

/-- A failed listed orientation is no obstruction to orientability: `twoCopies` is not
consistently oriented as listed, yet it is `Orientable`. -/
theorem twoCopies_not_oriented_but_orientable :
    ¬ ConsistentlyOriented twoCopies ∧ Orientable twoCopies := by decide

theorem twoCopies_reorient_second :
    ConsistentlyOriented (reorient twoCopies fun i => decide (i.val = 1)) := by decide

/-- For a `Valid` mesh a boundary edge rules orientability out: the disk's edge `(0, 1)` lies in
no other face. -/
theorem disk_not_orientable_of_boundary_edge : ¬ Orientable disk := by
  intro h
  obtain ⟨j, hj, -⟩ := h.edge_shared_of_valid (by decide) (i := ⟨0, by decide⟩) (a := 0) (b := 1)
    (by decide)
  exact hj (Fin.ext (Nat.lt_one_iff.mp j.2))

theorem rawLoop_linkEdgesList : linkEdgesList rawLoop 1 = [s(0, 0)] := by decide

/-- `linkDegree` counts link entries: the loop `s(0, 0)` counts once, not twice. -/
theorem rawLoop_linkDegree : linkDegree rawLoop 1 0 = 1 := by decide

/-- `faceCount` counts faces: a face traversing `s(0, 1)` several times counts once. -/
theorem rawRepeat_faceCount : faceCount rawRepeat s(0, 1) = 1 := by decide

/-- An `n × n` grid triangulation of the torus (`twist = false`) or, with the last row glued back
reversed, of the Klein bottle (`twist = true`). -/
private meta def gridMesh (n : ℕ) (twist : Bool) : Mesh ℕ :=
  let v : ℕ → ℕ → ℕ := fun i j =>
    if i = n then (if twist then (n - j) % n else j % n) else i * n + j % n
  ⟨(List.range n).flatMap fun i => (List.range n).flatMap fun j =>
    [[v i j, v (i + 1) j, v (i + 1) (j + 1)], [v i j, v (i + 1) (j + 1), v i (j + 1)]]⟩

#guard decide (ClosedSurface (gridMesh 4 false)) && decide (ClosedSurface (gridMesh 4 true))

-- 128 faces each: far beyond a search over all `2 ^ 128` flip assignments.
#guard chi (gridMesh 8 false) == 0 && chi (gridMesh 8 true) == 0
#guard decide (EdgesPaired (gridMesh 8 false)) && decide (EdgesPaired (gridMesh 8 true))
#guard decide (Orientable (gridMesh 8 false))
#guard !decide (Orientable (gridMesh 8 true))

end Cslib.Algorithms.Lean.Geometry.SurfaceMeshTests
