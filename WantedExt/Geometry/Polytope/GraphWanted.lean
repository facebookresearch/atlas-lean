/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Geometry.Polytope.Faces
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Graphs of convex polytopes: wanted statements

Balinski's theorem (the graph of a `d`-polytope is `d`-connected) and Steinitz's theorem (the
graphs of 3-polytopes are the planar 3-connected graphs).
-/

@[expose] public section

open MathlibExt.Geometry.Polytope

namespace MathlibExt.Geometry.Polytope.GraphWanted

/-- **Balinski's theorem.** The graph of a polytope `P = conv s` of dimension `d` is
`d`-connected: it has more than `d` vertices and stays connected after deleting any fewer than
`d` vertices (M. L. Balinski, 1961; G. M. Ziegler, *Lectures on Polytopes*, GTM 152,
Theorem 3.14, as cited in Ziegler, "Convex polytopes: extremal constructions and f-vector shapes",
IAS/Park City Math. Ser. 14 (2004), Section 1.2, arXiv:math/0411400v2). The polytope must be
nonempty. -/
theorem_wanted balinski {n d : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n))) (hs : s.Nonempty)
    (hd : dim s = d) :
    @SimpleGraph.IsVertexConnected _ (extremePoints_finite s).fintype d (graph s)

/-- **Steinitz's theorem.** A finite simple graph is the graph of a 3-dimensional convex polytope
if and only if it is planar and 3-connected. Here "graph of a 3-polytope" means isomorphic to
`graph s` for a finite set `s` in `ℝ^3` whose convex hull has nonempty interior; planarity is
the existence of a crossing-free straight-line drawing (by Fáry's theorem, equivalent to
planarity); and 3-connectivity includes having at least 4 vertices (E. Steinitz, 1922;
G. M. Ziegler, "Convex polytopes: extremal constructions and f-vector shapes", IAS/Park City
Math. Ser. 14 (2004), Theorem 1.2, arXiv:math/0411400v2). -/
theorem_wanted steinitz {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (G.IsPlanar ∧ G.IsVertexConnected 3) ↔
      ∃ s : Finset (EuclideanSpace ℝ (Fin 3)),
        (interior (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3))))).Nonempty ∧
          Nonempty (G ≃g graph s)

end MathlibExt.Geometry.Polytope.GraphWanted
