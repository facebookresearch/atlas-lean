/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM CUT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MAXIMUM CUT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxCut

/-!
# MAXIMUM CUT is NP-complete

An undirected graph and a bound `K`. The question is whether the vertices can be split into two
sets with at least `K` edges crossing between them, witnessed by a sublist of at least `K`
crossing edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of MAXIMUM CUT.** An instance of MAXIMUM CUT is a triple $(n, E, K)$ of a natural
number $n$ (the number of vertices), a finite list $E$ of ordered pairs of natural numbers (the
edges) and a natural number $K$ (the bound). -/
abbrev MaxCutInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Well-formed MAXIMUM CUT instances.** An instance $(n, E, K)$ of MAXIMUM CUT is well formed
when the list $E$ has no repeated entries and every pair $(u, v)$ in $E$ satisfies $u < n$,
$v < n$ and $u \ne v$, and the reversed pair $(v, u)$ does not occur in $E$. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible MAXIMUM CUT instances.** An instance $(n, E, K)$ of MAXIMUM CUT is feasible when
there are a finite set $S$ of natural numbers, all less than $n$, and a list $C$ of length at
least $K$ obtained from $E$ by deleting zero or more of its entries, such that every pair
$(u, v)$ in $C$ has exactly one of $u$ and $v$ in $S$. -/
def MaxCutFeasible
    (i : MaxCutInstance) : Prop :=
  ∃ S : Finset ℕ, (∀ v ∈ S, v < i.1) ∧
    ∃ cut : List (ℕ × ℕ), cut.Sublist i.2.1 ∧ i.2.2 ≤ cut.length ∧
      ∀ e ∈ cut, (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S)

open Classical in
/-- **MAXIMUM CUT as a decision problem.** The decision problem MAXIMUM CUT accepts a bitstring
$x$ exactly when decoding $x$ with the canonical bitstring encoding of instances of MAXIMUM CUT
succeeds and yields an instance that is well formed and feasible. All other bitstrings, including
those that fail to decode, are rejected. -/
noncomputable def maxCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutFeasible i)
  | none => false

/-- **MAXIMUM CUT is NP-complete.** The decision problem MAXIMUM CUT lies in NP, and every
decision problem in NP has a polynomial-time many-one reduction to MAXIMUM CUT.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), MAXIMUM CUT. -/
public theorem_wanted maxCut_npComplete :
    maxCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxCutDec

end MetaMathlibExt.Complexity.NPComplete.MaxCut
