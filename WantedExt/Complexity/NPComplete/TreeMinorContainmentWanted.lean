/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREE MINOR CONTAINMENT is NP-complete

Source:
J. Matoušek and R. Thomas, "On the complexity of finding iso- and other morphisms for partial
k-trees", Discrete Mathematics 108 (1992), 343-364, doi:10.1016/0012-365X(92)90687-B (minor
containment is NP-complete even when both graphs are trees of bounded diameter);
T. Gima, S. Kumabe, K. Kurita, Y. Okada and Y. Otachi, "Dichotomies for tree minor containment
with structural parameters", in *WALCOM: Algorithms and Computation*, Lecture Notes in Computer
Science 14549, Springer (2024), 392-405, doi:10.1007/978-981-97-0566-5_28 (arXiv:2311.03225,
Section 1, records the result of Matoušek and Thomas);
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 8 (1987), 285-303,
doi:10.1016/0196-6774(87)90043-5, Section 1 (MINOR CONTAINMENT "remains NP-complete" when both
graphs are trees, citing P. D. Seymour and P. W. Shor, private communications (1987)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import WantedExt.Complexity.NPComplete.GraphMinorTestingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreeMinorContainment

open GraphMinorTesting
  (GraphMinorTestingInstance hostGraph patternGraph GraphMinorTestingFeasible)

/-!
# TREE MINOR CONTAINMENT is NP-complete

INSTANCE: trees `G` and `H`.
QUESTION: does `G` contain `H` as a minor?

This is GRAPH MINOR TESTING (`GraphMinorTestingWanted`) restricted to instances in which both
graphs are trees. Gima, Kumabe, Kurita, Okada and Otachi (Section 1): "Even when both `G` and `H`
are trees, in which case we call the problem Tree Minor Containment, it remains NP-complete
[Matoušek and Thomas]. Furthermore, it remains NP-complete even if the diameters of both trees
are constant"; it is solvable in polynomial time when the maximum degree of `H` is bounded or
when both trees are caterpillars. Johnson's column records the same contrast with SUBGRAPH
ISOMORPHISM and SUBGRAPH HOMEOMORPHISM, which are polynomial-time solvable on trees.

The instance type (vertex count and edge list of `G`, then of `H`), the graphs `hostGraph` and
`patternGraph` (`Cslib.Complexity.Karp.edgeGraph` on `Fin n`), the parent's well-formedness
(two simple edge lists) and the question `GraphMinorTestingFeasible` (MathlibExt's
`MetaMathlibExt.IsMinor`: `H` is obtained from `G`, up to isomorphism, by deleting vertices,
deleting edges and contracting edges) are the parent's. The restriction adds that both graphs are
trees, Mathlib's `SimpleGraph.IsTree` (connected and acyclic; in particular nonempty).

Membership in NP: a minor model of `H` in `G` (disjoint connected branch sets) is a certificate,
and being a tree is checked in polynomial time. A tree on `n` vertices has `n - 1` edges, so the
binary vertex counts do not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed GRAPH MINOR TESTING instance (two simple edge
lists) in which both `G` and `H` are trees. -/
def WellFormed (i : GraphMinorTestingInstance) : Prop :=
  GraphMinorTesting.WellFormed i ∧ (hostGraph i).G.IsTree ∧ (patternGraph i).G.IsTree

open Classical in
/-- TREE MINOR CONTAINMENT as a decision problem over bitstrings. -/
noncomputable def treeMinorContainmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphMinorTestingInstance) x with
  | some i => decide (WellFormed i ∧ GraphMinorTestingFeasible i)
  | none => false

/-- **TREE MINOR CONTAINMENT is NP-complete.** Source: Matoušek and Thomas (1992); Gima,
Kumabe, Kurita, Okada and Otachi (2024), Section 1; Johnson (1987), Section 1. -/
public theorem_wanted treeMinorContainment_npComplete :
    treeMinorContainmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L treeMinorContainmentDec

end MetaMathlibExt.Complexity.NPComplete.TreeMinorContainment
