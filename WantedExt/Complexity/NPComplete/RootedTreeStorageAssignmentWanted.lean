/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROOTED TREE STORAGE ASSIGNMENT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR5] ROOTED TREE STORAGE ASSIGNMENT
(p. 227; transformation from ROOTED TREE ARRANGEMENT);
F. Gavril, "Some NP-complete problems on graphs", Proceedings of the 11th
Conference on Information Sciences and Systems, Johns Hopkins University,
Baltimore (1977), 91-95.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RootedTreeStorageAssignment

/-!
# ROOTED TREE STORAGE ASSIGNMENT is NP-complete

INSTANCE: a finite set `X`, a collection `C = {X₁, X₂, …, Xₙ}` of subsets of `X`, and a positive
integer `K`. QUESTION: is there a collection `C' = {X₁', X₂', …, Xₙ'}` of subsets of `X` such
that `Xᵢ ⊆ Xᵢ'` for `1 ≤ i ≤ n`, such that `∑ᵢ |Xᵢ' - Xᵢ| ≤ K`, and such that there is a directed
rooted tree `T = (X, A)` in which the elements of each `Xᵢ'`, `1 ≤ i ≤ n`, form a directed path?

`X` is `Fin N`. As in `RootedTreeArrangementWanted`, the rooted tree is a Mathlib
`SimpleGraph.IsTree` on `X` with a chosen root `r`, its arcs directed away from `r`. A directed
path of `T` runs away from the root: it is the vertex set of a simple path `p` from `u` to `v`
(`SimpleGraph.Walk.IsPath`) with `u` on the path from `r` to `v`, which in a tree means
`dist(r, v) = dist(r, u) + length(p)`. A path has at least one vertex, so an empty `Xᵢ` must be
enlarged; a rooted tree has a root, so `X = ∅` gives a no-instance. The sets `Xᵢ` are given as
duplicate-free lists.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the size `N` of `X = Fin N`, the sets `X₁, …, Xₙ` as lists, and the bound
`K`. -/
abbrev RootedTreeStorageAssignmentInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every set lists distinct elements of `X = Fin N`, and
`0 < K`. -/
def WellFormed (i : RootedTreeStorageAssignmentInstance) : Prop :=
  (∀ S ∈ i.2.1, S.Nodup ∧ ∀ x ∈ S, x < i.1) ∧ 0 < i.2.2

/-- Sets `Xᵢ' ⊆ X` that contain every listed element of `Xᵢ` below `N` (listed entries `≥ N` are
not tested; well-formed instances have none), with at most `K` elements not listed in `Xᵢ` added in
total, and a tree `T` on `X` with root `r` in which every `Xᵢ'` is the vertex set of a simple path
`p` from `u` to `v` running away from the root (`dist(r, v) = dist(r, u) + length(p)`). -/
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

/-- **ROOTED TREE STORAGE ASSIGNMENT is NP-complete.** Source: Garey and Johnson (1979), [SR5];
Gavril (1977). -/
public theorem_wanted rootedTreeStorageAssignment_npComplete :
    rootedTreeStorageAssignmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rootedTreeStorageAssignmentDec

end MetaMathlibExt.Complexity.NPComplete.RootedTreeStorageAssignment
