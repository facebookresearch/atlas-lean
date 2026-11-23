/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DECISION TREE (tests with at most three positives) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS15] DECISION TREE
(comment: remains NP-complete even if each test is `1` on at most three objects);
L. Hyafil and R. L. Rivest, "Constructing optimal binary decision trees is
NP-complete", Information Processing Letters 5 (1976), 15-17,
doi:10.1016/0020-0190(76)90095-8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DecisionTreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DecisionTreeThreePositives

/-!
# DECISION TREE (tests with at most three positives) is NP-complete

INSTANCE: a finite set `X` of objects, a collection `T = {T₁, ..., T_m}` of binary tests
`Tᵢ : X → {0, 1}`, and a positive integer `K`, where for each `Tᵢ ∈ T` there are at most three
distinct objects `x ∈ X` for which `Tᵢ(x) = 1`. QUESTION: is there a decision tree for `X`
using the tests in `T` that has total external path length `K` or less?

This is DECISION TREE (`MetaMathlibExt.Complexity.NPComplete.DecisionTree`) restricted to
instances in which every test has at most three positive objects; the instance type, decision
trees and the question are reused from that module unchanged. A test is a Boolean vector
indexed by the objects `0, ..., n - 1`, so its number of positive objects is its number of
`true` entries.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed DECISION TREE instance in which every test
is `1` on at most three objects. -/
def WellFormed (i : DecisionTree.DecisionTreeInstance) : Prop :=
  DecisionTree.WellFormed i ∧ ∀ T ∈ i.2.1, T.count true ≤ 3

open Classical in
/-- DECISION TREE (tests with at most three positives) as a decision problem over
bitstrings. -/
noncomputable def decisionTreeThreePositivesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DecisionTree.DecisionTreeInstance) x with
  | some i => decide (WellFormed i ∧ DecisionTree.DecisionTreeFeasible i)
  | none => false

/-- **DECISION TREE (tests with at most three positives) is NP-complete.** Source: Garey and
Johnson (1979), [MS15]; Hyafil and Rivest (1976). -/
public theorem_wanted decisionTreeThreePositives_npComplete :
    decisionTreeThreePositivesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L decisionTreeThreePositivesDec

end MetaMathlibExt.Complexity.NPComplete.DecisionTreeThreePositives
