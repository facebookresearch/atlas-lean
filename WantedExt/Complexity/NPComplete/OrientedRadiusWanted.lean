/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ORIENTED RADIUS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT64] ORIENTED DIAMETER, p. 205
(comment: "The variation in which 'diameter' is replaced by 'radius' is also NP-complete.");
V. Chvátal and C. Thomassen, "Distances in orientations of graphs", Journal of
Combinatorial Theory, Series B 24 (1978), 61-75,
doi:10.1016/0095-8956(78)90078-3 (also Stanford report STAN-CS-75-517, 1975: deciding whether
a graph admits an orientation of radius two is NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.OrientedDiameterWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OrientedRadius

/-!
# ORIENTED RADIUS is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: can the edges of `G`
be oriented so that the resulting directed graph is strongly connected and has radius no more
than `K`?

This is ORIENTED DIAMETER ([GT64], `OrientedDiameterWanted`) with "diameter" replaced by
"radius". The instance type, `OrientedDiameter.Graph`, `OrientedDiameter.WellFormed` (a simple
edge list on `Fin n` and `0 < K ≤ |V|`) and `OrientedDiameter.ReachWithin` (reachability along
at most `K` arcs) are reused unchanged, and an orientation is again a Mathlib `Digraph` `D`
with `(Graph i).IsOrientation D.Adj`.

Radius follows Chvátal and Thomassen: the radius of a strongly connected digraph is
`min_u max_v max {dist(u, v), dist(v, u)}`. So the radius is at most `K` exactly when some
centre `c` reaches every vertex `v`, and is reached from every vertex `v`, along at most `K`
arcs. That condition implies strong connectivity (every `u` reaches `c`, which reaches every
`v`), so the question's first condition is not repeated as a separate conjunct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some orientation of the graph has radius at most `K`: some centre `c` reaches every vertex,
and is reached from every vertex, along at most `K` arcs (hence the orientation is strongly
connected). -/
def OrientedRadiusFeasible (i : OrientedDiameter.OrientedDiameterInstance) : Prop :=
  ∃ D : Digraph (Fin i.1), (OrientedDiameter.Graph i).IsOrientation D.Adj ∧
    ∃ c, ∀ v, OrientedDiameter.ReachWithin D i.2.2 c v ∧ OrientedDiameter.ReachWithin D i.2.2 v c

open Classical in
/-- ORIENTED RADIUS as a decision problem over bitstrings. -/
noncomputable def orientedRadiusDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OrientedDiameter.OrientedDiameterInstance) x with
  | some i => decide (OrientedDiameter.WellFormed i ∧ OrientedRadiusFeasible i)
  | none => false

/-- **ORIENTED RADIUS is NP-complete.** Source: Garey and Johnson (1979), [GT64], comment;
Chvátal and Thomassen (1978). -/
public theorem_wanted orientedRadius_npComplete :
    orientedRadiusDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L orientedRadiusDec

end MetaMathlibExt.Complexity.NPComplete.OrientedRadius
