/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DECISION TREE: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS15] DECISION TREE;
L. Hyafil and R. L. Rivest, "Constructing optimal binary decision trees is
NP-complete", Information Processing Letters 5 (1976), 15-17,
doi:10.1016/0020-0190(76)90095-8.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Range

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DecisionTree

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

end MetaMathlibExt.Complexity.NPComplete.DecisionTree
