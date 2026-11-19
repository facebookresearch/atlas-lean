/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Geometry.SurfaceMesh
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic

namespace Cslib.Algorithms.Lean.Geometry.SurfaceMeshTests

open Cslib.Algorithms.Lean.Geometry.SurfaceMesh

def bowtie : Mesh (Fin 5) := ⟨[[0, 1, 2], [0, 3, 4]]⟩

def degenerate : Mesh (Fin 3) := ⟨[[0, 1, 1]]⟩

def subdivTetra : Mesh (Fin 5) :=
  ⟨[[0, 4, 1, 2], [0, 3, 1, 4], [0, 2, 3], [1, 3, 2]]⟩

theorem tetra_vertices : (vertices tetra).card = 4 := by decide

theorem tetra_edges : (edges tetra).card = 6 := by decide

theorem tetra_faces_length : tetra.faces.length = 4 := by decide

theorem tetra_chi : chi tetra = 2 := by decide

theorem tetra_closed : ClosedSurface tetra := by decide

theorem tetra_oriented : ConsistentlyOriented tetra := by decide

theorem tetra_orientable : Orientable tetra :=
  ⟨fun _ => false, by decide⟩

theorem cube_vertices : (vertices cube).card = 8 := by decide

theorem cube_edges : (edges cube).card = 12 := by decide

theorem cube_faces_length : cube.faces.length = 6 := by decide

theorem cube_chi : chi cube = 2 := by decide

theorem cube_closed : ClosedSurface cube := by decide

theorem cube_oriented : ConsistentlyOriented cube := by decide

theorem cube_orientable : Orientable cube :=
  ⟨fun _ => false, by decide⟩

theorem csaszar_vertices : (vertices csaszar).card = 7 := by decide +kernel

theorem csaszar_edges : (edges csaszar).card = 21 := by decide +kernel

theorem csaszar_faces_length : csaszar.faces.length = 14 := by decide

theorem csaszar_chi : chi csaszar = 0 := by decide +kernel

theorem csaszar_closed : ClosedSurface csaszar := by decide +kernel

theorem csaszar_oriented : ConsistentlyOriented csaszar := by decide

theorem csaszar_orientable : Orientable csaszar :=
  ⟨fun _ => false, by decide⟩

theorem bowtie_fails_link : ¬ VertexLinkCycle bowtie := by decide

theorem bowtie_fails_link_at_zero :
    ¬ ((∀ u ∈ linkVertsList bowtie 0, linkDegree bowtie 0 u = 2) ∧
      LinkConnected bowtie 0) := by decide

theorem degenerate_invalid : ¬ Valid degenerate := by decide

theorem subdivTetra_closed : ClosedSurface subdivTetra := by decide

theorem subdivTetra_oriented : ConsistentlyOriented subdivTetra := by decide

theorem subdivTetra_chi : chi subdivTetra = 2 := by decide

end Cslib.Algorithms.Lean.Geometry.SurfaceMeshTests
