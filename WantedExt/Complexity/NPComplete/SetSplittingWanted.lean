/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET SPLITTING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SET SPLITTING (hypergraph
2-coloring); S. Lovasz, "Coverings and colorings of hypergraphs" (1973).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetSplitting

/-!
# SET SPLITTING is NP-complete

A list of subsets of a universe of size `n`. The question is whether the universe can be split
into two parts so that every set meets both parts (hypergraph 2-colorability).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Set-splitting instances.** A set-splitting instance is a pair $(n, C)$ of a natural number
$n$, the size of the universe, and a list $C$ of lists of natural numbers, the subsets to be
split. -/
abbrev SetSplittingInstance := ℕ × List (List ℕ)

/-- **Well-formed set-splitting instances.** A set-splitting instance $(n, C)$, a natural number
$n$ together with a list $C$ of lists of natural numbers, is well formed when every list in $C$
has no repeated entries and all its entries are less than $n$. -/
def WellFormed (i : SetSplittingInstance) : Prop :=
  ∀ s ∈ i.2, s.Nodup ∧ ∀ x ∈ s, x < i.1

/-- **Feasible set-splitting instances.** A set-splitting instance $(n, C)$, a natural number $n$
together with a list $C$ of lists of natural numbers, is feasible when there is a finite set $S$
of natural numbers, all less than $n$, such that every list in $C$ has an entry in $S$ and an
entry not in $S$. -/
def SetSplittingFeasible
    (i : SetSplittingInstance) : Prop :=
  ∃ S : Finset ℕ, (∀ v ∈ S, v < i.1) ∧
    ∀ s ∈ i.2, (∃ x ∈ s, x ∈ S) ∧ ∃ y ∈ s, y ∉ S

open Classical in
/-- **The SET SPLITTING decision problem.** SET SPLITTING is the decision problem that accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a pair
$(n, C)$ of a natural number $n$ and a list $C$ of lists of natural numbers such that every list
in $C$ has no repeated entries and only entries less than $n$, and some finite set $S$ of natural
numbers less than $n$ contains an entry of every list in $C$ and misses an entry of every list in
$C$. Bitstrings that do not decode to such a pair are rejected. -/
noncomputable def setSplittingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetSplittingInstance) x with
  | some i => decide (WellFormed i ∧ SetSplittingFeasible i)
  | none => false

/-- **SET SPLITTING is NP-complete.** The SET SPLITTING decision problem belongs to NP, and every
decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), SET SPLITTING (hypergraph 2-coloring); S. Lovasz, "Coverings and
colorings of hypergraphs" (1973). -/
public theorem_wanted setSplitting_npComplete :
    setSplittingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L setSplittingDec

end MetaMathlibExt.Complexity.NPComplete.SetSplitting
