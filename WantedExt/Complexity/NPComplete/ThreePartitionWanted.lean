/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-PARTITION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), 3-PARTITION (strongly NP-
complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreePartition

/-!
# 3-PARTITION is NP-complete

A list of `3m` natural numbers and a target `B`. The question is whether the numbers can be
split into `m` triples each summing to `B`. The usual `B / 4 < a < B / 2` promise is not needed
when the triple size is explicit.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **3-partition instances.** An instance of 3-PARTITION is a pair $(a, B)$ of a finite list $a$
of natural numbers and a natural number $B$, the target sum. -/
abbrev ThreePartitionInstance := List ℕ × ℕ

/-- **Well-formed 3-partition instances.** A 3-partition instance $(a, B)$ is well formed when the
length of the list $a$ is a multiple of $3$. -/
def WellFormed (i : ThreePartitionInstance) : Prop :=
  i.1.length % 3 = 0

/-- **Feasible 3-partition instances.** Let $(a, B)$ be a 3-partition instance with
$a = (a_0, \dots, a_{N-1})$, and let $m = \lfloor N/3 \rfloor$. The instance is feasible when
there is a map $g : \{0, \dots, N-1\} \to \{0, \dots, m-1\}$ such that for every $t < m$ exactly
three indices $j$ satisfy $g(j) = t$, and the sum of $a_j$ over these indices equals $B$. -/
def ThreePartitionFeasible
    (i : ThreePartitionInstance) : Prop :=
  ∃ assign : List ℕ, assign.length = i.1.length ∧
    (∀ j < i.1.length, assign.getD j 0 < i.1.length / 3) ∧
    ∀ t < i.1.length / 3,
      ((List.range i.1.length).filter (fun j => assign.getD j 0 == t)).length = 3 ∧
      (Finset.range i.1.length).sum
        (fun j => if assign.getD j 0 = t then i.1.getD j 0 else 0) = i.2

open Classical in
/-- **3-PARTITION as a decision problem.** The decision problem 3-PARTITION accepts a bitstring
$x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a 3-partition instance
$(a, B)$ that is well formed (the length of the list $a$ is a multiple of $3$) and feasible (the
entries of $a$ can be split into triples each summing to $B$). Bitstrings that do not decode to
an instance are rejected. -/
noncomputable def threePartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreePartitionInstance) x with
  | some i => decide (WellFormed i ∧ ThreePartitionFeasible i)
  | none => false

/-- **3-PARTITION is NP-complete.** The decision problem 3-PARTITION on bitstrings is in NP, and
every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), 3-PARTITION (strongly NP-complete). -/
public theorem_wanted threePartition_npComplete :
    threePartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threePartitionDec

end MetaMathlibExt.Complexity.NPComplete.ThreePartition
