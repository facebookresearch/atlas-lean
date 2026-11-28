/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST WEIGHT-CONSTRAINED PATH for directed graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND30] SHORTEST
WEIGHT-CONSTRAINED PATH (p. 214; attributed there to N. Megiddo, 1977, private communication;
transformation from PARTITION), comment "Also NP-complete for directed graphs".
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ShortestWeightConstrainedPathDefs
public import CSLibExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestWeightConstrainedPathDirected

open MetaMathlibExt.Complexity.NPComplete.ShortestWeightConstrainedPath
  (ShortestWeightConstrainedPathInstance)

/-- The arcs of the instance as `(tail, head)` pairs. -/
def arcs (i : ShortestWeightConstrainedPathInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun e => (e.1, e.2.1)

/-- The `(length, weight)` of the listed arc from `a` to `b`; `(0, 0)` if there is none. Under
`WellFormed` at most one listed arc goes from `a` to `b`. -/
def arcData (i : ShortestWeightConstrainedPathInstance) (a b : ℕ) : ℕ × ℕ :=
  ((i.2.1.find? fun e => decide ((e.1, e.2.1) = (a, b))).map fun e => e.2.2).getD (0, 0)

/-- Well-formedness of an instance: the arcs join distinct in-range vertices, no two listed arcs
have the same tail and head, every length and weight is positive, `s, t ∈ V`, and `K, W` are
positive. -/
def WellFormed (i : ShortestWeightConstrainedPathInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧ 0 < e.2.2.1 ∧ 0 < e.2.2.2) ∧
    (arcs i).Nodup ∧ i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ 0 < i.2.2.2.2.1 ∧ 0 < i.2.2.2.2.2

/-- A simple directed path from `s` to `t` whose total weight is at most `W` and whose total
length is at most `K`. -/
def ShortestWeightConstrainedPathDirectedFeasible
    (i : ShortestWeightConstrainedPathInstance) : Prop :=
  ∃ p : List ℕ, DirectedTwoDisjointConnectingPaths.IsDirectedPath (arcs i) i.2.2.1 i.2.2.2.1 p ∧
    ((p.zip p.tail).map fun e => (arcData i e.1 e.2).2).sum ≤ i.2.2.2.2.2 ∧
    ((p.zip p.tail).map fun e => (arcData i e.1 e.2).1).sum ≤ i.2.2.2.2.1

open Classical in
/-- SHORTEST WEIGHT-CONSTRAINED PATH for directed graphs as a decision problem over bitstrings. -/
noncomputable def shortestWeightConstrainedPathDirectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestWeightConstrainedPathInstance) x with
  | some i => decide (WellFormed i ∧ ShortestWeightConstrainedPathDirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ShortestWeightConstrainedPathDirected
