/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DECISION TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS15] DECISION TREE;
L. Hyafil and R. L. Rivest, "Constructing optimal binary decision trees is
NP-complete", Information Processing Letters 5 (1976), 15-17,
doi:10.1016/0020-0190(76)90095-8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Range

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DecisionTree

/-!
# DECISION TREE is NP-complete

INSTANCE: a finite set `X` of objects, a collection `T = {T₁, ..., T_m}` of binary tests
`Tᵢ : X → {0, 1}`, and a positive integer `K`. QUESTION: is there a decision tree for `X` using
the tests in `T` that has total external path length `K` or less?

A decision tree is a binary tree whose non-leaf vertices are labelled by tests from `T` and
whose leaves are labelled by objects from `X`; the edge from a non-leaf vertex to its left child
is labelled `0` and to its right child `1`. If `T_{i₁}, O₁, ..., T_{i_k}, O_k` are the vertex
and edge labels on the path from the root to a leaf labelled `x`, then `x` must be the unique
object with `T_{i_j}(x) = O_j` for all `j`. The total external path length is the sum, over
all leaves, of the number of edges from the root to the leaf.

Objects are `0, ..., n - 1`; test `t` sends object `x` to entry `x` of the `t`-th listed
Boolean vector.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A binary decision tree: a leaf labelled by an object, or a vertex labelled by a test with a
`0`-child and a `1`-child. -/
inductive Tree where
  | leaf (x : ℕ)
  | node (t : ℕ) (zero one : Tree)

/-- An instance: the number of objects `n`, the tests (test `t` is a Boolean vector of length
`n`), and the bound `K`. -/
abbrev DecisionTreeInstance := ℕ × List (List Bool) × ℕ

/-- The outcome of test `t` on object `x`. -/
def test (i : DecisionTreeInstance) (t x : ℕ) : Bool :=
  (i.2.1.getD t []).getD x false

/-- Well-formedness of an instance: every test is a Boolean vector of length `n`, and
`0 < K`. -/
def WellFormed (i : DecisionTreeInstance) : Prop :=
  (∀ T ∈ i.2.1, T.length = i.1) ∧ 0 < i.2.2

/-- `Identifies i S tr`: `tr` uses only listed tests, and the label of each leaf of `tr` is the
unique object of `S` consistent with the test outcomes on the path to it (each step keeps the
objects of `S` with the edge's outcome). -/
def Identifies (i : DecisionTreeInstance) : Finset ℕ → Tree → Prop
  | S, .leaf x => S = {x}
  | S, .node t z o => t < i.2.1.length ∧
      Identifies i (S.filter (fun x => test i t x = false)) z ∧
      Identifies i (S.filter (fun x => test i t x = true)) o

/-- The total external path length of a tree whose root is at depth `d`: the sum over its
leaves of their depths. -/
def externalPathLength : ℕ → Tree → ℕ
  | d, .leaf _ => d
  | d, .node _ z o => externalPathLength (d + 1) z + externalPathLength (d + 1) o

/-- A decision tree for the objects `0, ..., n - 1` with total external path length at most
`K`. -/
def DecisionTreeFeasible (i : DecisionTreeInstance) : Prop :=
  ∃ tr, Identifies i (Finset.range i.1) tr ∧ externalPathLength 0 tr ≤ i.2.2

open Classical in
/-- DECISION TREE as a decision problem over bitstrings. -/
noncomputable def decisionTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DecisionTreeInstance) x with
  | some i => decide (WellFormed i ∧ DecisionTreeFeasible i)
  | none => false

/-- **DECISION TREE is NP-complete.** Source: Garey and Johnson (1979), [MS15]; Hyafil and
Rivest (1976). -/
public theorem_wanted decisionTree_npComplete :
    decisionTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L decisionTreeDec

end MetaMathlibExt.Complexity.NPComplete.DecisionTree
