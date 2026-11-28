/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM TEST SET FOR LOCATING SINGLE LINK FAILURES: definitions

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

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Relation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FaultDetectionDirectedGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumTestSetLinkFailures

open MetaMathlibExt.Complexity.NPComplete.FaultDetectionDirectedGraphs

/-- The test `p = (u, v)` fails when the link `(a, b)` fails: `u` reaches `a` and `b` reaches
`v`. This does not test that `a → b` is an arc; when it is, as for the links of the well-formed
DAG, the condition says the link lies on a directed path from `u` to `v`. -/
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

end MetaMathlibExt.Complexity.NPComplete.MinimumTestSetLinkFailures
