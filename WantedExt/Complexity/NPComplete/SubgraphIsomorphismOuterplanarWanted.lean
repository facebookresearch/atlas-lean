/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SUBGRAPH ISOMORPHISM for connected outerplanar graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT48] SUBGRAPH ISOMORPHISM (the
unrestricted problem);
M. M. Sysło, "The subgraph isomorphism problem for outerplanar graphs", Theoretical Computer
Science 17 (1982), 91-97, doi:10.1016/0304-3975(82)90133-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SubgraphIsomorphismWanted
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import WantedExt.GraphTheory.BookThicknessOfSubdivisionsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SubgraphIsomorphismOuterplanar

open MetaMathlibExt.Complexity.NPComplete.SubgraphIsomorphism
  (SubgraphIsomorphismInstance GraphHost)
open MathlibExt.GraphTheory.BookThicknessOfSubdivisionsWanted (HasBookEmbedding)

/-!
# SUBGRAPH ISOMORPHISM for connected outerplanar graphs is NP-complete

INSTANCE: connected outerplanar graphs `G = (V₁, E₁)` and `H = (V₂, E₂)`. QUESTION: does `G`
contain a subgraph isomorphic to `H`, i.e., is there an injective map from `V₂` to `V₁` sending
every edge of `H` to an edge of `G`?

This is the restriction of SUBGRAPH ISOMORPHISM
(`WantedExt.Complexity.NPComplete.SubgraphIsomorphismWanted`) to instances in which both graphs
are connected and outerplanar. The instance type, the host graph `G`, the parent
well-formedness condition (both edge lists simple) and the question are that module's; the
restriction is added to `WellFormed`. Connectivity is Mathlib's `SimpleGraph.Connected` (which
requires at least one vertex).

A graph is outerplanar when it has a planar embedding with every vertex on the boundary of the
outer face. Outerplanarity is stated as book thickness at most `1`, which Bernhart and Kainen
("The book thickness of a graph", J. Combin. Theory Ser. B 27 (1979), 320-331,
doi:10.1016/0095-8956(79)90021-2) prove equivalent to it: the repository's book-embedding
predicate `HasBookEmbedding G 1` (from
`WantedExt.GraphTheory.BookThicknessOfSubdivisionsWanted`, also used by
`BookThicknessTwoWanted`) asks for an injective placement of the vertices on a line (the spine)
such that no two edges with alternating endpoints `v ≺ x ≺ w ≺ y` exist, since with one page all
edges share a page. Drawing the spine as a circle, the edges become non-crossing chords and every
vertex lies on the outer face. MathlibExt's `SimpleGraph.IsPlanar` (crossing-free straight-line
drawings) carries no outer-face condition, so it is not used.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The pattern graph `H` of the instance. -/
def GraphPattern (i : SubgraphIsomorphismInstance) : SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2

/-- Well-formedness of an instance: it is a well-formed SUBGRAPH ISOMORPHISM instance (both edge
lists simple), and the host `G` and the pattern `H` are connected and outerplanar (have a
one-page book embedding). -/
def WellFormed (i : SubgraphIsomorphismInstance) : Prop :=
  SubgraphIsomorphism.WellFormed i ∧ (GraphHost i).Connected ∧ HasBookEmbedding (GraphHost i) 1 ∧
    (GraphPattern i).Connected ∧ HasBookEmbedding (GraphPattern i) 1

open Classical in
/-- SUBGRAPH ISOMORPHISM for connected outerplanar graphs as a decision problem over
bitstrings. -/
noncomputable def subgraphIsomorphismOuterplanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SubgraphIsomorphismInstance) x with
  | some i => decide (WellFormed i ∧ SubgraphIsomorphism.SubgraphIsomorphismFeasible i)
  | none => false

/-- **SUBGRAPH ISOMORPHISM is NP-complete for connected outerplanar graphs.** Source: Garey and
Johnson (1979), [GT48]; Sysło (1982). -/
public theorem_wanted subgraphIsomorphismOuterplanar_npComplete :
    subgraphIsomorphismOuterplanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L subgraphIsomorphismOuterplanarDec

end MetaMathlibExt.Complexity.NPComplete.SubgraphIsomorphismOuterplanar
