/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The largest planar graphs of positive combinatorial curvature (Open Problem Garden 157)

Open Problem Garden, What is the largest graph of positive curvature? (M. DeVos, B. Mohar): what is
the largest connected planar graph of minimum degree `3` which has everywhere positive combinatorial
curvature, but is not a prism or antiprism?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Rat.Defs
public import Mathlib.Dynamics.PeriodicPts.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.LargestPositiveCurvatureGraphOpenGardenProblem157Wanted

/-!
Source: Open Problem Garden, What is the largest graph of positive curvature? (node 157; M. DeVos
and B. Mohar), http://www.openproblemgarden.org/op/what_is_the_largest_graph_of_positive_curvature.
UnsolvedMath record UM-00003328 (`OPG-157`), dataset ulamai/UnsolvedMath v1.8.0.

A graph embedded in the sphere is a finite simple connected graph `G` with a rotation system `ρ` (a
cyclic order of the darts at each vertex) of Euler characteristic `2`, `|V| - |E| + |F| = 2`; by the
Heffter-Edmonds rotation principle these are the cellular embeddings in the sphere, and every
embedding of a connected graph in the sphere is cellular. Faces are the cycles of the face
permutation `(u, v) ↦ ρ (v, u)`; the size of a face is the length of its boundary walk, and the
faces at `v` are counted once per corner, so the curvature `1 - deg(v)/2 + ∑_{f ∼ v} 1/|f|` and the
face vector `f(v)` are those of Ghidelli, §1.1. Prisms and antiprisms are transcribed from Ghidelli,
§1.1 (a prism of order `N` has exactly `2N` vertices, two faces of size `N`, `N` faces of size `4`
and `f(v) = {4, 4, N}` at every vertex; an antiprism has `2N` vertices, two faces of size `N`, `2N`
triangles and `f(v) = {3, 3, 3, N}`); every prism and antiprism with more than `8` vertices meets
this literal definition. The answer to the question is formalized as: every planar PCC graph has at
most `208` vertices, and one has exactly `208`.
-/

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A rotation system on `G` (a cellular embedding of `G` in an orientable surface): a permutation
`ρ` of the darts that keeps the tail of each dart and runs through all darts at a vertex in one
cycle (their cyclic order around the vertex). -/
def IsRotationSystem (ρ : Equiv.Perm G.Dart) : Prop :=
  (∀ d, (ρ d).fst = d.fst) ∧ ∀ d d' : G.Dart, d.fst = d'.fst → ∃ k : ℕ, (ρ ^ k) d = d'

/-- The face permutation of the embedding: the facial walk that traverses the dart `(u, v)`
continues with the dart `ρ (v, u)`. -/
def facePerm (ρ : Equiv.Perm G.Dart) (d : G.Dart) : G.Dart :=
  ρ d.symm

/-- The size of the face whose boundary walk traverses `d`: the length of that walk, edges counted
with multiplicity. -/
noncomputable def faceSize (ρ : Equiv.Perm G.Dart) (d : G.Dart) : ℕ :=
  Function.minimalPeriod (facePerm G ρ) d

/-- The darts with tail `v`; they correspond to the edges at `v`, and to the corners of the faces
at `v` (the corner between the dart `(u, v)` and the next dart `facePerm (u, v)` of the walk). -/
def dartsAt (v : V) : Finset G.Dart :=
  Finset.univ.filter fun d => d.fst = v

/-- The number of faces of the embedding: `∑_d 1 / |face(d)|`. -/
noncomputable def numFaces (ρ : Equiv.Perm G.Dart) : ℚ :=
  ∑ d : G.Dart, (1 : ℚ) / faceSize G ρ d

/-- The embedding is in the sphere: `G` is connected and `|V| - |E| + |F| = 2`. -/
def IsSpherical (ρ : Equiv.Perm G.Dart) : Prop :=
  G.Connected ∧ (Fintype.card V : ℚ) - (Fintype.card G.Dart : ℚ) / 2 + numFaces G ρ = 2

/-- The combinatorial curvature `1 - deg(v)/2 + ∑_{f ∼ v} 1/|f|` at `v`, the sum running over the
faces at `v` with multiplicity (one term per corner). -/
noncomputable def curvature (ρ : Equiv.Perm G.Dart) (v : V) : ℚ :=
  1 - ((dartsAt G v).card : ℚ) / 2 + ∑ d ∈ dartsAt G v, (1 : ℚ) / faceSize G ρ d

/-- The face vector `f(v)`: the multiset of sizes of the faces at `v` (one per corner). -/
noncomputable def faceVector (ρ : Equiv.Perm G.Dart) (v : V) : Multiset ℕ :=
  (dartsAt G v).val.map (faceSize G ρ)

/-- The number of faces of size `k` (each such face has `k` darts). -/
noncomputable def numFacesOfSize (ρ : Equiv.Perm G.Dart) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun d : G.Dart => faceSize G ρ d = k).card / k

/-- A prism of order `N` (Ghidelli, §1.1): exactly `2N` vertices, two faces of size `N` and `N`
faces of size `4`, and `f(v) = {4, 4, N}` at every vertex. -/
def IsPrism (ρ : Equiv.Perm G.Dart) : Prop :=
  ∃ N : ℕ, Fintype.card V = 2 * N ∧ numFacesOfSize G ρ N = 2 ∧ numFacesOfSize G ρ 4 = N ∧
    ∀ v, faceVector G ρ v = {4, 4, N}

/-- An antiprism of order `N` (Ghidelli, §1.1): exactly `2N` vertices, two faces of size `N` and
`2N` faces of size `3`, and `f(v) = {3, 3, 3, N}` at every vertex. -/
def IsAntiprism (ρ : Equiv.Perm G.Dart) : Prop :=
  ∃ N : ℕ, Fintype.card V = 2 * N ∧ numFacesOfSize G ρ N = 2 ∧ numFacesOfSize G ρ 3 = 2 * N ∧
    ∀ v, faceVector G ρ v = {3, 3, 3, N}

/-- A planar PCC graph (Ghidelli, Definition 1.1): a simple connected graph embedded in the sphere
with positive combinatorial curvature and degree at least `3` at every vertex, which is not a prism
or an antiprism. -/
def IsPlanarPCC (ρ : Equiv.Perm G.Dart) : Prop :=
  IsRotationSystem G ρ ∧ IsSpherical G ρ ∧ (∀ v, 0 < curvature G ρ v) ∧
    (∀ v, 3 ≤ (dartsAt G v).card) ∧ ¬ IsPrism G ρ ∧ ¬ IsAntiprism G ρ

/-- The answer to DeVos and Mohar's question: the largest planar PCC graphs have exactly `208`
vertices, that is, every planar PCC graph has at most `208` vertices and some has exactly `208`. -/
def largestPlanarPCCGraphHas208Vertices : Prop :=
  (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (ρ : Equiv.Perm G.Dart), IsPlanarPCC G ρ → Fintype.card V ≤ 208) ∧
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj)
      (ρ : Equiv.Perm G.Dart), IsPlanarPCC G ρ ∧ Fintype.card V = 208

/--
Resolved true: Ghidelli proves (Theorem 3.1) that every simple connected graph embedded in the
sphere with positive combinatorial curvature and degree at least `3` at every vertex, other than a
prism or an antiprism, has at most `208` vertices, and exhibits (Section 18) known such graphs with
exactly `208` vertices, so the largest have `208` vertices. Source: Open Problem Garden, What is the
largest graph of positive curvature? (node 157; M. DeVos and B. Mohar),
http://www.openproblemgarden.org/op/what_is_the_largest_graph_of_positive_curvature; resolution: L.
Ghidelli, On the largest planar graphs with everywhere positive combinatorial curvature, J. Combin.
Theory Ser. B 158 (2023), 226-263; arXiv:1708.08502, Definition 1.1 (planar PCC graph) and Theorem
3.1 (every planar PCC graph has at most 208 vertices), answering DeVos and Mohar's question
completely; Section 18 exhibits the known planar PCC graphs with exactly 208 vertices, so Theorem
3.1 is sharp, https://arxiv.org/abs/1708.08502.
-/
public theorem_wanted largestPlanarPCCGraphHas208Vertices_holds :
    largestPlanarPCCGraphHas208Vertices

end MathlibExt.GraphTheory.LargestPositiveCurvatureGraphOpenGardenProblem157Wanted
