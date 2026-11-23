/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUADRATIC ASSIGNMENT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), QUADRATIC ASSIGNMENT
PROBLEM; S. Sahni and T. Gonzalez, "P-complete approximation problems" (1976).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticAssignment

/-!
# QUADRATIC ASSIGNMENT is NP-complete

Nonnegative integer flow and distance matrices and a bound `K`. The question is whether some
permutation (assignment of facilities to locations) has total cost at most `K`: the sum over
all pairs of flow times distance between the assigned locations.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of QUADRATIC ASSIGNMENT.** An instance of quadratic assignment is a tuple
$(n, F, D, K)$ consisting of a natural number $n$ (the size), a flow matrix $F$ and a distance
matrix $D$, each given as a list of rows that are lists of natural numbers, and a natural
number $K$ (the cost bound). -/
abbrev QuadraticAssignmentInstance := ℕ × List (List ℕ) × List (List ℕ) × ℕ

/-- **Well-formed quadratic assignment instances.** An instance $(n, F, D, K)$ of quadratic
assignment is well formed when the flow matrix $F$ and the distance matrix $D$ each have
exactly $n$ rows and every row of each has length $n$. -/
def WellFormed (i : QuadraticAssignmentInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    i.2.2.1.length = i.1 ∧ ∀ row ∈ i.2.2.1, row.length = i.1

/-- **Feasible quadratic assignment instances.** An instance $(n, F, D, K)$ of quadratic
assignment is feasible when there is a permutation $\pi$ of the numbers $0, \dots, n - 1$ such
that
$$
\sum_{a < n} \sum_{b < n} F_{a b} \, D_{\pi(a) \pi(b)} \le K.
$$
Here $F_{a b}$ is entry $b$ of row $a$ of $F$, and likewise for $D$; an entry that is missing,
because the matrix has too few rows or the row is too short, is read as $0$. -/
def QuadraticAssignmentFeasible
    (i : QuadraticAssignmentInstance) : Prop :=
  ∃ perm : List ℕ, perm.Perm (List.range i.1) ∧
    (Finset.range i.1).sum (fun a => (Finset.range i.1).sum (fun b =>
      (i.2.1.getD a []).getD b 0 *
        (i.2.2.1.getD (perm.getD a 0) []).getD (perm.getD b 0) 0)) ≤ i.2.2.2

open Classical in
/-- **QUADRATIC ASSIGNMENT as a decision problem.** The decision problem QUADRATIC ASSIGNMENT
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
quadratic assignment instance that is well formed and feasible; bitstrings that do not decode
are rejected. -/
noncomputable def quadraticAssignmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := QuadraticAssignmentInstance) x with
  | some i => decide (WellFormed i ∧ QuadraticAssignmentFeasible i)
  | none => false

/-- **QUADRATIC ASSIGNMENT is NP-complete.** The decision problem QUADRATIC ASSIGNMENT lies in NP,
and every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), QUADRATIC ASSIGNMENT PROBLEM; S. Sahni and T. Gonzalez,
"P-complete approximation problems" (1976). -/
public theorem_wanted quadraticAssignment_npComplete :
    quadraticAssignmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L quadraticAssignmentDec

end MetaMathlibExt.Complexity.NPComplete.QuadraticAssignment
