/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO TRIANGLES for planar graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT11] PARTITION INTO TRIANGLES;
D. S. Johnson, "The NP-completeness column: an ongoing guide" (tenth edition), Journal of
Algorithms 5 (1984), 147-160, doi:10.1016/0196-6774(84)90045-2 (update to [GT11]:
"NP-complete for planar graphs [4,22]");
F. Berman, D. Johnson, T. Leighton, P. W. Shor and L. Snyder, "Generalized planar matching",
Journal of Algorithms 11 (1990), 153-184, doi:10.1016/0196-6774(90)90001-U;
M. E. Dyer and A. M. Frieze, "Planar 3DM is NP-complete", Journal of Algorithms 7 (1986),
174-184, doi:10.1016/0196-6774(86)90002-7.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PartitionIntoTrianglesPlanarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoTrianglesPlanar

/-!
# PARTITION INTO TRIANGLES for planar graphs is NP-complete

INSTANCE: a planar graph `G = (V, E)` with `|V| = 3q` for some integer `q`. QUESTION: can the
vertices of `G` be partitioned into `q` disjoint sets `V₁, ..., V_q`, each containing exactly
three vertices, such that each `Vᵢ` induces a triangle in `G`?

This is the restriction of PARTITION INTO TRIANGLES ([GT11], `PartitionIntoTrianglesWanted`)
to planar graphs. The instance type, `PartitionIntoTriangles.Graph` (the edge list as a
`SimpleGraph (Fin n)`) and `PartitionIntoTriangles.PartitionIntoTrianglesFeasible` (a list of
vertex triples whose concatenation is a permutation of all vertices, each triple without
repeats and pairwise adjacent) are the parent's, unchanged. `WellFormed` keeps the parent's
simple-edge-list condition and adds the restriction (`SimpleGraph.IsPlanar` from
`MathlibExt.Combinatorics.SimpleGraph.Planarity`, as in `PlanarThreeDimensionalMatchingWanted`)
and the instance condition `|V| = 3q` (`3 ∣ n`), which the parent leaves to the feasibility
predicate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTITION INTO TRIANGLES is NP-complete for planar graphs.** Source: Garey and Johnson
(1979), [GT11]; Johnson, NP-completeness column (1984); Berman, Johnson, Leighton, Shor and
Snyder (1990); Dyer and Frieze (1986). -/
public theorem_wanted partitionIntoTrianglesPlanar_npComplete :
    partitionIntoTrianglesPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoTrianglesPlanarDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoTrianglesPlanar
