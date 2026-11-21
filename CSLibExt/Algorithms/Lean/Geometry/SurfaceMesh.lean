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

@[expose] public section

namespace Cslib.Algorithms.Lean.Geometry.SurfaceMesh

structure Mesh (V : Type _) [DecidableEq V] where
  faces : List (List V)

def directedEdgesOfFace {V : Type _} [DecidableEq V] (f : List V) :
    List (V × V) :=
  f.zip (f.rotate 1)

def allDirectedEdges {V : Type _} [DecidableEq V] (M : Mesh V) :
    List (V × V) :=
  M.faces.flatMap directedEdgesOfFace

def edgesList {V : Type _} [DecidableEq V] (M : Mesh V) : List (Sym2 V) :=
  (allDirectedEdges M).map (fun p => Sym2.mk p.1 p.2)

def verticesList {V : Type _} [DecidableEq V] (M : Mesh V) : List V :=
  (allDirectedEdges M).flatMap (fun p => [p.1, p.2])

def vertices {V : Type _} [DecidableEq V] (M : Mesh V) : Finset V :=
  (verticesList M).toFinset

def edges {V : Type _} [DecidableEq V] (M : Mesh V) : Finset (Sym2 V) :=
  (edgesList M).toFinset

def chi {V : Type _} [DecidableEq V] (M : Mesh V) : Int :=
  ((vertices M).card : Int) - ((edges M).card : Int) + (M.faces.length : Int)

def Valid {V : Type _} [DecidableEq V] (M : Mesh V) : Prop :=
  (∀ f ∈ M.faces, 3 ≤ f.length ∧ f.Nodup) ∧
    M.faces.Pairwise (fun f₁ f₂ =>
      ¬ List.IsRotated f₁ f₂ ∧ ¬ List.IsRotated f₁.reverse f₂)

def faceCount {V : Type _} [DecidableEq V] (M : Mesh V) (e : Sym2 V) :
    Nat :=
  (M.faces.filter (fun f => decide (e ∈ (directedEdgesOfFace f).map
    (fun p => Sym2.mk p.1 p.2)))).length

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

def VertexLinkCycle {V : Type _} [DecidableEq V] (M : Mesh V) : Prop :=
  ∀ v ∈ verticesList M,
    (∀ u ∈ linkVertsList M v, linkDegree M v u = 2) ∧ LinkConnected M v

def ClosedSurface {V : Type _} [DecidableEq V] (M : Mesh V) : Prop :=
  Valid M ∧ EdgeManifold M ∧ VertexLinkCycle M

def ConsistentlyOriented {V : Type _} [DecidableEq V] (M : Mesh V) :
    Prop :=
  (∀ d ∈ allDirectedEdges M,
    (M.faces.filter (fun f => decide (d ∈ directedEdgesOfFace f))).length ≤ 1) ∧
  (∀ d ∈ allDirectedEdges M, (d.2, d.1) ∈ allDirectedEdges M)

def reorient {V : Type _} [DecidableEq V] (M : Mesh V)
    (flip : Fin M.faces.length → Bool) : Mesh V :=
  ⟨List.ofFn (fun i => if flip i then M.faces[i].reverse else M.faces[i])⟩

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

instance Orientable.decidable {V : Type _} [DecidableEq V] (M : Mesh V) :
    Decidable (Orientable M) := by
  unfold Orientable
  infer_instance

def tetra : Mesh (Fin 4) :=
  ⟨[[0, 1, 2], [0, 3, 1], [0, 2, 3], [1, 3, 2]]⟩

def cube : Mesh (Fin 8) :=
  ⟨[[0, 1, 2, 3], [4, 7, 6, 5], [0, 4, 5, 1], [3, 2, 6, 7],
    [0, 3, 7, 4], [1, 5, 6, 2]]⟩

def csaszar : Mesh (Fin 7) :=
  ⟨[[0, 1, 3], [0, 3, 2], [1, 2, 4], [1, 4, 3], [2, 3, 5], [2, 5, 4],
    [3, 4, 6], [3, 6, 5], [4, 5, 0], [4, 0, 6], [5, 6, 1], [5, 1, 0],
    [6, 0, 2], [6, 2, 1]]⟩

end Cslib.Algorithms.Lean.Geometry.SurfaceMesh
