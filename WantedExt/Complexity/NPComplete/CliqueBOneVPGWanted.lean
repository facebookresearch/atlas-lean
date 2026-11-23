/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE on B₁-VPG graphs is NP-complete

Source:
M. Middendorf and F. Pfeiffer, "The max clique problem in classes of string-graphs", Discrete
Mathematics 108 (1992), 365-372, doi:10.1016/0012-365X(92)90688-C;
recorded in S. Felsner, K. Knauer, G. B. Mertzios and T. Ueckerdt, "Intersection graphs of
L-shapes and segments in the plane", Discrete Applied Mathematics 206 (2016),
doi:10.1016/j.dam.2016.01.028, Section 1;
A. Asinowski, E. Cohen, M. C. Golumbic, V. Limouzy, M. Lipshteyn and M. Stern, "Vertex
intersection graphs of paths on a grid", Journal of Graph Algorithms and Applications 16(2)
(2012), 129-150, doi:10.7155/jgaa.00253 (the class `B₁-VPG`);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueBOneVPG

/-!
# CLIQUE on B₁-VPG graphs is NP-complete

INSTANCE: a `B₁-VPG` graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain a clique of size `K` or more, i.e., a set `V' ⊆ V` with `|V'| ≥ K`
such that every two vertices in `V'` are joined by an edge?

This is CLIQUE ([GT19]) restricted to the graph class `B₁-VPG` (ISGCI `gc_1064`) of Asinowski,
Cohen, Golumbic, Limouzy, Lipshteyn and Stern (2012): the vertex intersection graphs of paths
with at most one bend on a grid, i.e., graphs with a family of such paths, one per vertex, two
distinct vertices being adjacent exactly when their paths share a grid point. Middendorf and
Pfeiffer (1992) show that the complement of every even subdivision of every graph is an
intersection graph of axis-aligned L-shapes (a horizontal and a vertical segment meeting at an
endpoint of both) in two rotations; as Felsner, Knauer, Mertzios and Ueckerdt (2016) record,
this implies that maximum clique is NP-complete on these graphs, which are `B₁-VPG` graphs.

The graph is simple and given by an edge list on `Fin n`. A path with at most one bend on the
grid `ℕ × ℕ` is given by three grid points `(a, c, b)`, its legs `a`-`c` and `c`-`b` being
horizontal or vertical (a leg of length `0` is allowed, so straight paths and single grid points
are included); its grid points are those of the two legs. The lattice points of an
axis-parallel leg from `p` to `q` are the points of `ℕ × ℕ` between them in both coordinates.
Paths of distinct vertices are distinct as point sets (the family is in one-to-one
correspondence with `V`). Since all corners lie on grid points, two such paths meet in the
plane exactly when they share a grid point, and every finite intersection model of paths with
at most one bend can be moved to the integer grid by replacing coordinates by their ranks, so
the class does not depend on these encoding choices. The path model is not part of the input.
The bound `0 < K ≤ |V|` is the instance class of [GT19].

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev CliqueBOneVPGInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CliqueBOneVPGInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- A grid path with at most one bend, given by its endpoints `a`, `b` and its corner `c`
(legs `a`-`c` and `c`-`b`). -/
abbrev BendPath := (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)

/-- The grid points between `p` and `q` in both coordinates; for an axis-parallel leg from `p`
to `q`, the lattice points of the leg. -/
def legPoints (p q : ℕ × ℕ) : Set (ℕ × ℕ) :=
  {r | min p.1 q.1 ≤ r.1 ∧ r.1 ≤ max p.1 q.1 ∧ min p.2 q.2 ≤ r.2 ∧ r.2 ≤ max p.2 q.2}

/-- The grid points of a path: those of its two legs. -/
def pathPoints (P : BendPath) : Set (ℕ × ℕ) :=
  legPoints P.1 P.2.1 ∪ legPoints P.2.1 P.2.2

/-- Both legs of the path are horizontal or vertical. -/
def IsBendPath (P : BendPath) : Prop :=
  (P.1.1 = P.2.1.1 ∨ P.1.2 = P.2.1.2) ∧ (P.2.1.1 = P.2.2.1 ∨ P.2.1.2 = P.2.2.2)

/-- `G` is a `B₁-VPG` graph: there are grid paths with at most one bend, one per vertex and
pairwise distinct as point sets, such that two distinct vertices are adjacent exactly when their
paths share a grid point. -/
def IsBOneVPG {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ P : Fin n → BendPath, (∀ v, IsBendPath (P v)) ∧ Function.Injective (fun v => pathPoints (P v)) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ (pathPoints (P u) ∩ pathPoints (P v)).Nonempty)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), `0 < K ≤ n`, and the
graph is a `B₁-VPG` graph. -/
def WellFormed (i : CliqueBOneVPGInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ IsBOneVPG (Graph i)

/-- The graph has a clique of size `K` or more. -/
def CliqueBOneVPGFeasible (i : CliqueBOneVPGInstance) : Prop :=
  ∃ S : Finset (Fin i.1), i.2.2 ≤ S.card ∧ (Graph i).IsClique (S : Set (Fin i.1))

open Classical in
/-- CLIQUE on `B₁-VPG` graphs as a decision problem over bitstrings. -/
noncomputable def cliqueBOneVPGDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := CliqueBOneVPGInstance) x with
  | some i => decide (WellFormed i ∧ CliqueBOneVPGFeasible i)
  | none => false

/-- **CLIQUE on `B₁-VPG` graphs is NP-complete.** Source: Middendorf and Pfeiffer (1992), as
recorded by Felsner, Knauer, Mertzios and Ueckerdt (2016); Asinowski et al. (2012) (the class);
Garey and Johnson (1979), [GT19]. -/
public theorem_wanted cliqueBOneVPG_npComplete :
    cliqueBOneVPGDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cliqueBOneVPGDec

end MetaMathlibExt.Complexity.NPComplete.CliqueBOneVPG
