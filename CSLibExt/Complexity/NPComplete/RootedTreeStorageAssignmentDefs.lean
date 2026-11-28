/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROOTED TREE STORAGE ASSIGNMENT: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR5] ROOTED TREE STORAGE ASSIGNMENT
(p. 227; transformation from ROOTED TREE ARRANGEMENT);
F. Gavril, "Some NP-complete problems on graphs", Proceedings of the 11th
Conference on Information Sciences and Systems, Johns Hopkins University,
Baltimore (1977), 91-95.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RootedTreeStorageAssignment

/-- An instance: the size `N` of `X = Fin N`, the sets `X₁, …, Xₙ` as lists, and the bound
`K`. -/
abbrev RootedTreeStorageAssignmentInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every set lists distinct elements of `X = Fin N`, and
`0 < K`. -/
def WellFormed (i : RootedTreeStorageAssignmentInstance) : Prop :=
  (∀ S ∈ i.2.1, S.Nodup ∧ ∀ x ∈ S, x < i.1) ∧ 0 < i.2.2

/-- Supersets `Xᵢ' ⊇ Xᵢ` with at most `K` added elements in total, and a tree `T` on `X` with
root `r` in which every `Xᵢ'` is the vertex set of a simple path `p` from `u` to `v` running away
from the root (`dist(r, v) = dist(r, u) + length(p)`). -/
def RootedTreeStorageAssignmentFeasible (i : RootedTreeStorageAssignmentInstance) : Prop :=
  ∃ X' : Fin i.2.1.length → Finset (Fin i.1),
    (∀ j, ∀ x : Fin i.1, (x : ℕ) ∈ i.2.1[j] → x ∈ X' j) ∧
    ∑ j, ((X' j).filter fun x : Fin i.1 => (x : ℕ) ∉ i.2.1[j]).card ≤ i.2.2 ∧
    ∃ T : SimpleGraph (Fin i.1), T.IsTree ∧ ∃ r : Fin i.1,
      ∀ j, ∃ u v : Fin i.1, ∃ p : T.Walk u v, p.IsPath ∧ p.support.toFinset = X' j ∧
        T.dist r v = T.dist r u + p.length

open Classical in
/-- ROOTED TREE STORAGE ASSIGNMENT as a decision problem over bitstrings. -/
noncomputable def rootedTreeStorageAssignmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RootedTreeStorageAssignmentInstance) x with
  | some i => decide (WellFormed i ∧ RootedTreeStorageAssignmentFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RootedTreeStorageAssignment
