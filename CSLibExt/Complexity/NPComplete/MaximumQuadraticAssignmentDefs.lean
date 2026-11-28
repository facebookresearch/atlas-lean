/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.QuadraticAssignmentDefs

/-!
# MAXIMUM QUADRATIC ASSIGNMENT: definitions

INSTANCE: nonnegative symmetric `n × n` matrices `A = (a_{k,l})` and `B = (b_{i,j})`, and a
positive integer `K`. QUESTION: is there a permutation `π : [1..n] → [1..n]` such that
`∑_{i ≠ j} a_{π(i),π(j)} b_{i,j} ≥ K`?

This is the decision version of Crescenzi and Kann's MAXIMUM QUADRATIC ASSIGNMENT.
Arkin, Hassin and Sviridenko (Section 1) state that the problem, which in their version also
has a linear term `∑_i c_{i,π(i)}`, is NP-hard; the version here is theirs with `C = 0`, which
contains their special case MAX DISPERSION (`A` a clique on `p` vertices plus `n - p` isolated
vertices, Section 2): with `B` the adjacency matrix of a graph `G`, the measure is at least
`p (p - 1)` iff `G` has a clique on `p` vertices. Membership in NP: `π` is a certificate.

Indices are `0, ..., n - 1`. The instance has the shape of
`QuadraticAssignment.QuadraticAssignmentInstance`, and `WellFormed` extends that module's
well-formedness (both matrices are `n × n`) with symmetry and `0 < K`. Entries are natural
numbers, so the matrices are nonnegative. As there, a permutation is a list `perm` that is a
permutation of `[0, ..., n - 1]`, read as `π(i) = perm[i]`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, MAXIMUM
QUADRATIC ASSIGNMENT;
E. M. Arkin, R. Hassin and M. Sviridenko, "Approximating the maximum quadratic assignment
problem", Information Processing Letters 77 (2001), 13-16,
doi:10.1016/S0020-0190(00)00151-4.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumQuadraticAssignment

/-- An instance: the size `n`, the matrices `A` and `B` as lists of rows, and the bound `K`. -/
abbrev MaximumQuadraticAssignmentInstance :=
  QuadraticAssignment.QuadraticAssignmentInstance

/-- The entry in row `k` and column `l` of a matrix given as a list of rows. -/
def entry (M : List (List ℕ)) (k l : ℕ) : ℕ :=
  (M.getD k []).getD l 0

/-- The `n × n` matrix `M` is symmetric. -/
def IsSymmetric (n : ℕ) (M : List (List ℕ)) : Prop :=
  ∀ k < n, ∀ l < n, entry M k l = entry M l k

/-- Well-formedness of an instance: `A` and `B` are `n × n` matrices
(`QuadraticAssignment.WellFormed`), both are symmetric, and `K` is positive. -/
def WellFormed (i : MaximumQuadraticAssignmentInstance) : Prop :=
  QuadraticAssignment.WellFormed i ∧ IsSymmetric i.1 i.2.1 ∧ IsSymmetric i.1 i.2.2.1 ∧
    0 < i.2.2.2

/-- Some permutation `π` of `[0, ..., n - 1]` has `∑_{i ≠ j} a_{π(i),π(j)} b_{i,j} ≥ K`. -/
def MaximumQuadraticAssignmentFeasible (i : MaximumQuadraticAssignmentInstance) : Prop :=
  ∃ perm : List ℕ, perm.Perm (List.range i.1) ∧
    i.2.2.2 ≤ ∑ a ∈ Finset.range i.1, ∑ b ∈ (Finset.range i.1).filter (· ≠ a),
      entry i.2.1 (perm.getD a 0) (perm.getD b 0) * entry i.2.2.1 a b

open Classical in
/-- MAXIMUM QUADRATIC ASSIGNMENT as a decision problem over bitstrings. -/
noncomputable def maximumQuadraticAssignmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumQuadraticAssignmentInstance) x with
  | some i => decide (WellFormed i ∧ MaximumQuadraticAssignmentFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumQuadraticAssignment
