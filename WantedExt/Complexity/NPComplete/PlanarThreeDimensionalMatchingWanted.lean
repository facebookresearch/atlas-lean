/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR 3-DIMENSIONAL MATCHING is NP-complete

Source:
M. E. Dyer and A. M. Frieze, "Planar 3DM is NP-complete", Journal of Algorithms 7(2) (1986),
174-184, doi:10.1016/0196-6774(86)90002-7;
S. Borgwardt and S. Patterson, "On the computational complexity of finding a sparse Wasserstein
barycenter", Journal of Combinatorial Optimization 41(3) (2021), arXiv:1910.07568, Section 2.2
(definition of planar 3-dimensional matching; "P3DM itself is NP-hard", credited to Dyer and
Frieze);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SP1] 3-DIMENSIONAL MATCHING.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import WantedExt.Complexity.NPComplete.ThreeDimensionalMatchingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarThreeDimensionalMatching

open MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatching

/-!
# PLANAR 3-DIMENSIONAL MATCHING is NP-complete

INSTANCE: an instance of [SP1] 3-DIMENSIONAL MATCHING, a set `M ⊆ W × X × Y` where `W`, `X`, `Y`
are disjoint sets with `|W| = |X| = |Y| = q`, whose element-triple incidence graph is planar: the
bipartite graph with a vertex for each element of `W ∪ X ∪ Y` and for each triple of `M`, and an
edge joining each triple to the three elements it contains.
QUESTION: does `M` contain a matching of size `q`, that is, `M' ⊆ M` with `|M'| = q` and no two
triples of `M'` agreeing in any coordinate?

The instance, its well-formedness and the matching question are those of
`WantedExt.Complexity.NPComplete.ThreeDimensionalMatchingWanted` (elements `0, …, q - 1` of each
of `W`, `X`, `Y`; triples as a list). Here the triples are distinct (`M` is a set), and planarity
is `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing; by Fáry's theorem the same as
planarity) of `incidenceGraph`, whose vertices are `w` (`0 ≤ w < q`), `q + x`, `2q + y`, and
`3q + j` for the `j`-th triple. Dyer and Frieze prove NP-completeness even when every element
occurs in at most three triples; those instances belong to this class.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The element-triple incidence graph: vertex `3q + j` (the `j`-th triple `(w, x, y)`) is
adjacent to the element vertices `w`, `q + x` and `2q + y`. -/
def incidenceGraph (i : ThreeDimensionalMatchingInstance) :
    SimpleGraph (Fin (3 * i.1 + i.2.length)) :=
  SimpleGraph.fromRel fun u v => ∃ j < i.2.length, u.val = 3 * i.1 + j ∧
    (v.val = (i.2.getD j (0, 0, 0)).1 ∨ v.val = i.1 + (i.2.getD j (0, 0, 0)).2.1 ∨
      v.val = 2 * i.1 + (i.2.getD j (0, 0, 0)).2.2)

/-- Well-formedness of an instance: a well-formed 3DM instance with distinct triples whose
incidence graph is planar. -/
def WellFormed (i : ThreeDimensionalMatchingInstance) : Prop :=
  ThreeDimensionalMatching.WellFormed i ∧ i.2.Nodup ∧ (incidenceGraph i).IsPlanar

/-- `M` contains a matching of size `q` (the 3DM question). -/
def PlanarThreeDimensionalMatchingFeasible (i : ThreeDimensionalMatchingInstance) : Prop :=
  ThreeDimensionalMatchingFeasible i

open Classical in
/-- PLANAR 3-DIMENSIONAL MATCHING as a decision problem over bitstrings. -/
noncomputable def planarThreeDimensionalMatchingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeDimensionalMatchingInstance) x with
  | some i => decide (WellFormed i ∧ PlanarThreeDimensionalMatchingFeasible i)
  | none => false

/-- **PLANAR 3-DIMENSIONAL MATCHING is NP-complete.** Source: Dyer and Frieze (1986). -/
public theorem_wanted planarThreeDimensionalMatching_npComplete :
    planarThreeDimensionalMatchingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarThreeDimensionalMatchingDec

end MetaMathlibExt.Complexity.NPComplete.PlanarThreeDimensionalMatching
