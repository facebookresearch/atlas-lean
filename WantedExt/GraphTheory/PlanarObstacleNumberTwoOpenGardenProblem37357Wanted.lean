/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A planar graph with obstacle number greater than one (Open Problem Garden 37357)

Open Problem Garden, Obstacle number of planar graphs (H. Alpert, C. Koch and J. D. Laison): does
there exist a planar graph with obstacle number greater than `1`? Is there some `k` such that every
planar graph has obstacle number at most `k`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MathlibExt.GraphTheory.PlanarObstacleNumberTwoOpenGardenProblem37357Wanted

/-!
Source: Open Problem Garden, Obstacle number of planar graphs (node 37357; H. Alpert, C. Koch and J.
D. Laison), http://www.openproblemgarden.org/op/obstacle_number_of_planar_graphs. UnsolvedMath
record UM-00003119 (`OPG-37357`), dataset ulamai/UnsolvedMath v1.8.0.

Only the first question, which is resolved, is stated here; the second (a uniform bound for planar
graphs) is open and is the OpenConjectures entry `OpenGardenProblem37357`. Obstacle representations
follow Berman et al., Section 1 (Alpert, Koch and Laison's definition): distinct points for the
vertices and connected subsets of the plane as obstacles, no obstacle meeting the drawing (vertex
points and edge segments) and every non-edge segment meeting an obstacle; the page says polygonal
obstacles, and allowing any connected set only makes the statement stronger. Graphs are finite
simple graphs on `Fin n`; planarity is MathlibExt's `SimpleGraph.IsPlanar` (a crossing-free
straight-line drawing). Obstacle number greater than `1` means no representation with `0` or `1`
obstacles.
-/

/-- `G` has an obstacle representation with `h` obstacles (Alpert-Koch-Laison, as stated by Berman
et al., Section 1): distinct points `p i` for the vertices and `h` connected sets in the plane such
that no obstacle meets the drawing of `G` (its vertex points and edge segments), while the segment
of every non-edge meets at least one obstacle. -/
def HasObstacleRepresentation {n : ℕ} (G : SimpleGraph (Fin n)) (h : ℕ) : Prop :=
  ∃ (p : Fin n → ℝ × ℝ) (O : Fin h → Set (ℝ × ℝ)), Function.Injective p ∧
    (∀ k, IsConnected (O k)) ∧ (∀ k i, p i ∉ O k) ∧
    (∀ i j, G.Adj i j → ∀ k, Disjoint (segment ℝ (p i) (p j)) (O k)) ∧
    ∀ i j, i ≠ j → ¬ G.Adj i j → ∃ k, (segment ℝ (p i) (p j) ∩ O k).Nonempty

/-- The first question on the source page, with a positive answer: some planar graph has obstacle
number greater than `1`, i.e. has no obstacle representation with at most one obstacle. -/
def planarGraphObstacleNumberAboveOne : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsPlanar ∧ ∀ h ≤ 1, ¬ HasObstacleRepresentation G h

/--
Resolved true: Berman, Chappell, Faudree, Gimbel, Hartman and Williams proved, with a
computer-assisted lower bound, that the icosahedron, a planar graph, has obstacle number `2` with
arbitrary connected obstacles. Source: Open Problem Garden, Obstacle number of planar graphs (node
37357; H. Alpert, C. Koch and J. D. Laison),
http://www.openproblemgarden.org/op/obstacle_number_of_planar_graphs; resolution: L. W. Berman, G.
G. Chappell, J. R. Faudree, J. Gimbel, C. Hartman and G. I. Williams, Graphs with obstacle number
greater than one, J. Graph Algorithms Appl. 21(6) (2017), 1107-1119, doi:10.7155/jgaa.00452;
arXiv:1606.03782, Proposition 5.3(2): obs(I) = 2 for the icosahedron I (lower bound
computer-assisted via a SAT instance, Section 5); abstract: this answers 'a question of Alpert,
Koch, & Laison asking whether all planar graphs have obstacle number at most 1'; Section 1 defines
obstacle representations with connected obstacles, https://doi.org/10.7155/jgaa.00452.
-/
public theorem_wanted planarGraphObstacleNumberAboveOne_holds : planarGraphObstacleNumberAboveOne

end MathlibExt.GraphTheory.PlanarObstacleNumberTwoOpenGardenProblem37357Wanted
