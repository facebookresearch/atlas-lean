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

theorem bowtie_fails_link_at_zero :
    ¬ ((∀ u ∈ linkVertsList bowtie 0, linkDegree bowtie 0 u = 2) ∧
      LinkConnected bowtie 0) := by decide

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

theorem disk_not_orientable : ¬ Orientable disk := by decide

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
#guard decide (Orientable (gridMesh 8 false))
#guard !decide (Orientable (gridMesh 8 true))

end Cslib.Algorithms.Lean.Geometry.SurfaceMeshTests
