/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF WEAK RECTANGLE VISIBILITY GRAPHS is NP-complete

Source:
T. C. Shermer, "On rectangle visibility graphs III. External visibility and complexity", in
Proceedings of the 8th Canadian Conference on Computational Geometry (CCCG 1996), Carleton
University Press (1996), 234-239, doi:10.1515/9780773591134-041 (Section 1: the definitions of
bands of visibility, rectangle visibility graphs and weak rectangle visibility graphs used below;
Section 4, Theorem 4.5, "RVG Recognition is NP-complete", and Section 5: "RVG Recognition is
NP-complete, for weak, collinear, or noncollinear RVGs").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.WeakRectangleVisibilityRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeakRectangleVisibilityRecognition

/-!
# RECOGNITION OF WEAK RECTANGLE VISIBILITY GRAPHS is NP-complete

INSTANCE: a graph `G = (V, E)`.
QUESTION: is `G` a weak rectangle visibility graph?

Shermer (Section 1): "Let `R = {R_i}` be a collection of pairwise disjoint closed rectangles in
the plane. Two rectangles `R_i` and `R_j` will be called visible if there is a closed
non-degenerate rectangular region `B_ij` (called a band of visibility) such that one side of
`B_ij` is contained in a side of `R_i`, the opposite side of `B_ij` is contained in a side of
`R_j`, and `B_ij` does not intersect the interior of any rectangle in `R`. [...] The visibility
graph of `R` is the graph of the visibility relation on vertex-set `R`; [...] A graph is called a
rectangle visibility graph, or RVG, if it is the visibility graph of some collection `R` of
rectangles [...]. A graph is called a weak RVG if it is a subgraph of an RVG. In weak layouts we
are allowed to embed two nonadjacent vertices as rectangles that are visible." The rectangles
are aligned with the coordinate axes (ISGCI, class `gc_725`: "vertices are represented by
rectangles that are aligned with the axes and edges are horizontal or vertical lines of sight
(note that not every line of sight need to be an edge)").

Definitions:
* `Rect`: an axis-parallel rectangle given by its coordinates `(x₁, x₂, y₁, y₂)`; its closed
  region is `region = [x₁, x₂] × [y₁, y₂]` and its interior is `interiorRegion =
  (x₁, x₂) × (y₁, y₂)`; it is non-degenerate when `x₁ < x₂` and `y₁ < y₂`;
* `Rect.side r k`: the four sides of `r` (`0` left `{x₁} × [y₁, y₂]`, `1` right
  `{x₂} × [y₁, y₂]`, `2` bottom `[x₁, x₂] × {y₁}`, `3` top `[x₁, x₂] × {y₂}`), and
  `oppositeSide` pairs left with right and bottom with top;
* `IsRectangleLayout R`: `R` assigns each vertex a non-degenerate rectangle, and the closed
  rectangles of distinct vertices are disjoint;
* `IsBandOfVisibility R u v B`: `B` is a closed non-degenerate rectangle, some side of `B` is
  contained in a side of `R u` and the opposite side of `B` in a side of `R v`, and `B` meets
  the interior of no rectangle of the layout (the rectangles of `u` and `v` included). A band is
  axis-parallel because one of its sides lies in an axis-parallel side, so it is a `Rect` too;
* `IsWeakRectangleVisibilityGraph G`: some rectangle layout of the vertices of `G` has a band of
  visibility for every edge of `G`. This is "a subgraph of an RVG": the visibility graph of the
  layout is an RVG containing `G`; conversely, the rectangles that a layout of an RVG `H ⊇ G`
  assigns to the vertices of `G` form a layout in which every edge of `G` still has its band,
  since removing rectangles removes only obstacles.

The graph is given by an edge list on `Fin n` (`Cslib.Complexity.Karp.edgeGraph`). Shermer
notes that the problem is in NP "as one can guess a layout and verify it".

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RECOGNITION OF WEAK RECTANGLE VISIBILITY GRAPHS is NP-complete.** Source: Shermer (1996),
Theorem 4.5 and Section 5. -/
public theorem_wanted weakRectangleVisibilityRecognition_npComplete :
    weakRectangleVisibilityRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weakRectangleVisibilityRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.WeakRectangleVisibilityRecognition
