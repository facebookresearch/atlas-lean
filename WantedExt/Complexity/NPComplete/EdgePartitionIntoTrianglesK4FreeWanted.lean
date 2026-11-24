/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE PARTITION INTO TRIANGLES for K₄-free graphs is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3 (1982),
182-195, doi:10.1016/0196-6774(82)90018-9 (problem [1] EDGE-PARTITION INTO TRIANGLES and its
comment);
I. Holyer, "The NP-completeness of some edge-partition problems", SIAM Journal on Computing 10
(1981), 713-717, doi:10.1137/0210054;
C. J. Colbourn, "The complexity of completing partial Latin squares", Discrete Applied
Mathematics 8 (1984), 25-30, doi:10.1016/0166-218X(84)90075-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.EdgePartitionIntoTrianglesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgePartitionIntoTrianglesK4Free

open EdgePartitionIntoTriangles (EdgePartitionIntoTrianglesInstance Graph
  EdgePartitionIntoTrianglesFeasible)

/-!
# EDGE PARTITION INTO TRIANGLES for K₄-free graphs is NP-complete

INSTANCE: a graph `G = (V, E)` containing no complete subgraph on four vertices.
QUESTION: is there a partition `E = E₁ ∪ … ∪ E_k` into disjoint sets such that each `Eᵢ` forms
a triangle (a copy of `K₃`)?

Johnson (1982), problem [1] EDGE-PARTITION INTO TRIANGLES: "INSTANCE: Graph `G = (V, E)`.
QUESTION: Is there a partition `E = E₁ ∪ … ∪ E_k` into disjoint sets such that each `Eᵢ` is
isomorphic to the complete graph `K₃`? Reference. Holyer. Transformation from 3SAT. Comment.
Remains NP-complete even if `G` contains no complete subgraph of size greater than 3."
Holyer's abstract proves the unrestricted problem NP-complete. Colbourn (1984) proves it
NP-complete for tripartite graphs ("a reduction from partitioning tripartite graphs into
triangles. This in turn is shown to be NP-complete using a recent result of Holyer"); a
tripartite graph has no `K₄`, so this is a published proof of the restricted case. Membership
in NP: the triangles are a certificate.

This is `EdgePartitionIntoTrianglesWanted` restricted to `K₄`-free graphs: the same instance,
graph (`Cslib.Complexity.Karp.edgeGraph`), well-formedness and question
(`EdgePartitionIntoTrianglesFeasible`: a set of 3-cliques covering every edge exactly once),
reused unchanged, with Mathlib's `SimpleGraph.CliqueFree 4` added to `WellFormed`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed EDGE PARTITION INTO TRIANGLES instance (a
simple edge list on `Fin n`) whose graph has no 4-clique. -/
def WellFormed (i : EdgePartitionIntoTrianglesInstance) : Prop :=
  EdgePartitionIntoTriangles.WellFormed i ∧ (Graph i).CliqueFree 4

open Classical in
/-- EDGE PARTITION INTO TRIANGLES for `K₄`-free graphs as a decision problem over bitstrings. -/
noncomputable def edgePartitionIntoTrianglesK4FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgePartitionIntoTrianglesInstance) x with
  | some i => decide (WellFormed i ∧ EdgePartitionIntoTrianglesFeasible i)
  | none => false

/-- **EDGE PARTITION INTO TRIANGLES for `K₄`-free graphs is NP-complete.** Source: Johnson (1982),
recording Holyer (1981); Colbourn (1984) for tripartite graphs. -/
public theorem_wanted edgePartitionIntoTrianglesK4Free_npComplete :
    edgePartitionIntoTrianglesK4FreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L edgePartitionIntoTrianglesK4FreeDec

end MetaMathlibExt.Complexity.NPComplete.EdgePartitionIntoTrianglesK4Free
