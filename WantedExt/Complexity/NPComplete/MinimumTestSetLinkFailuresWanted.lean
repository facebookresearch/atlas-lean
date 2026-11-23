/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM TEST SET FOR LOCATING SINGLE LINK FAILURES is NP-complete

Source:
T. Ibaraki, T. Kameda and S. Toida, "On minimal test sets for locating single link failures in
networks", IEEE Transactions on Computers C-30(3) (1981), 182-190, doi:10.1109/TC.1981.1675754
(abstract: in an acyclic directed network a test injects a signal at a vertex, monitors it at
another vertex, and reveals whether a failed link lies on a path between them; finding a minimal
test set that uniquely locates any single link failure is in general NP-complete);
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
145-159 (records that the NP-hardness of the vertex-failure problem of Garey and Johnson's
[MS18] is shared by this edge-failure problem, citing Ibaraki, Kameda and Toida).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Relation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.FaultDetectionDirectedGraphsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumTestSetLinkFailures

open MetaMathlibExt.Complexity.NPComplete.FaultDetectionDirectedGraphs

/-!
# MINIMUM TEST SET FOR LOCATING SINGLE LINK FAILURES is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)` whose arcs (links) are subject to failure, and a
positive integer `K`. QUESTION: is there a set of at most `K` tests that locates any single
failed link, if any? A test `(u, v)` injects a signal at a vertex `u`, monitors it at another
vertex `v`, and fails exactly when the failed link lies on some directed path from `u` to `v`.
Assuming at most one link fails, the test set locates a failed link, if any, when the set of
failed tests determines the failure: every link fails some test (distinguishing it from no
failure), and for every two distinct links some test fails for exactly one of them.

The instance, its well-formedness and the digraph are those of [MS18] FAULT DETECTION IN
DIRECTED GRAPHS (`WantedExt.Complexity.NPComplete.FaultDetectionDirectedGraphsWanted`): vertex
count `n`, a list of distinct arcs between vertices below `n`, the digraph acyclic, and `K`
positive. Unlike [MS18], a test may join any two distinct vertices and the objects that fail are
the arcs. The link `(a, b)` lies on a directed path from `u` to `v` exactly when `u` reaches `a`
and `b` reaches `v` (`Relation.ReflTransGen` of the arc relation): in an acyclic digraph the
directed walks `u ⇝ a` and `b ⇝ v` and the arc `(a, b)` concatenate to a directed path.
Vertices on no arc lie on no link and reach no link, so the binary vertex count does not make
the problem succinct. A locating test set separates the `|A| + 1` failure states (no failure,
or one of the `|A|` links), and an inclusion-minimal family separating `N` states has at most
`N - 1` members (J. A. Bondy, "Induced subsets", J. Combin. Theory Ser. B 12 (1972), 201-202),
so a test set of at most `|A|` tests is a polynomial-size certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The test `p = (u, v)` fails when the link `(a, b)` fails: the link lies on a directed path
from `u` to `v`, i.e. `u` reaches `a` and `b` reaches `v`. -/
def TestFails (i : FaultDetectionDirectedGraphsInstance) (p : Fin i.1 × Fin i.1)
    (a b : Fin i.1) : Prop :=
  Relation.ReflTransGen (Graph i).Adj p.1 a ∧ Relation.ReflTransGen (Graph i).Adj b p.2

/-- Some set `T` of at most `K` tests, each joining two distinct vertices, locates any single
failed link: every link fails some test, and every two distinct links are separated by a test
that fails for exactly one of them. -/
def MinimumTestSetLinkFailuresFeasible (i : FaultDetectionDirectedGraphsInstance) : Prop :=
  ∃ T : Finset (Fin i.1 × Fin i.1), T.card ≤ i.2.2 ∧ (∀ p ∈ T, p.1 ≠ p.2) ∧
    ∀ a b, (Graph i).Adj a b →
      (∃ p ∈ T, TestFails i p a b) ∧
        ∀ a' b', (Graph i).Adj a' b' → (a, b) ≠ (a', b') →
          ∃ p ∈ T, ¬ (TestFails i p a b ↔ TestFails i p a' b')

open Classical in
/-- MINIMUM TEST SET FOR LOCATING SINGLE LINK FAILURES as a decision problem over bitstrings. -/
noncomputable def minimumTestSetLinkFailuresDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FaultDetectionDirectedGraphsInstance) x with
  | some i => decide (FaultDetectionDirectedGraphs.WellFormed i ∧
      MinimumTestSetLinkFailuresFeasible i)
  | none => false

/-- **MINIMUM TEST SET FOR LOCATING SINGLE LINK FAILURES is NP-complete.** Source: Ibaraki,
Kameda and Toida (1981); Johnson (1985). -/
public theorem_wanted minimumTestSetLinkFailures_npComplete :
    minimumTestSetLinkFailuresDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumTestSetLinkFailuresDec

end MetaMathlibExt.Complexity.NPComplete.MinimumTestSetLinkFailures
