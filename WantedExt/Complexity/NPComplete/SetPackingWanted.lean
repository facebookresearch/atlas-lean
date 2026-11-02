/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET PACKING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SET PACKING; R. M. Karp,
"Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetPacking

/-!
# SET PACKING is NP-complete

A list of subsets of a universe of size `n` and a bound `K`. The question is whether at least
`K` of the subsets are pairwise disjoint. The chosen sublist must have no duplicate sets: two
copies of the same set do not count as disjoint.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Set-packing instances.** A set-packing instance is a triple $(n, C, K)$ consisting of a
natural number $n$, the size of the universe, a finite list $C$ of finite lists of natural numbers,
the subsets, and a natural number $K$, the bound. -/
abbrev SetPackingInstance := ℕ × List (List ℕ) × ℕ

/-- **Well-formed set-packing instances.** A set-packing instance $(n, C, K)$ is well formed when
every list $s$ in $C$ has no repeated entries and every entry of $s$ is less than $n$, that is,
each member of $C$ lists the elements of a subset of $\{0, \dots, n - 1\}$ without repetition. -/
def WellFormed (i : SetPackingInstance) : Prop :=
  ∀ s ∈ i.2.1, s.Nodup ∧ ∀ x ∈ s, x < i.1

/-- **Feasible set-packing instances.** A set-packing instance $(n, C, K)$ is feasible when there
is a sublist $D$ of $C$ (a list obtained from $C$ by deleting entries while keeping their order)
with no repeated entries and at least $K$ entries such that any two distinct entries of $D$ have
no element in common.

In particular two copies of the same list, even of the empty list, cannot both be chosen. -/
def SetPackingFeasible
    (i : SetPackingInstance) : Prop :=
  ∃ sub : List (List ℕ), sub.Sublist i.2.1 ∧ sub.Nodup ∧ i.2.2 ≤ sub.length ∧
    ∀ s1 ∈ sub, ∀ s2 ∈ sub, s1 ≠ s2 → ∀ x, x ∈ s1 → x ∉ s2

open Classical in
/-- **The SET PACKING decision problem.** SET PACKING is the decision problem that accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a set-packing
instance $(n, C, K)$ that is both well formed and feasible: every list in $C$ has no repeated
entries and only entries less than $n$, and some sublist of $C$ with no repeated entries and at
least $K$ entries has no element in common between any two of its distinct entries. Bitstrings
that do not decode to a set-packing instance are rejected. -/
noncomputable def setPackingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetPackingInstance) x with
  | some i => decide (WellFormed i ∧ SetPackingFeasible i)
  | none => false

/-- **SET PACKING is NP-complete.** The SET PACKING decision problem lies in NP, and every
decision problem $L$ in NP has a polynomial-time many-one reduction to SET PACKING.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), SET PACKING; R. M. Karp, "Reducibility among combinatorial
problems" (1972). -/
public theorem_wanted setPacking_npComplete :
    setPackingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L setPackingDec

end MetaMathlibExt.Complexity.NPComplete.SetPacking
