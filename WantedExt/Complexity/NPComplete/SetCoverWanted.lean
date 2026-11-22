/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET COVER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), SET COVER; R. M. Karp,
"Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetCover

/-!
# SET COVER is NP-complete

A universe of size `n`, a list of subsets, and a bound `K`. The question is whether at most `K`
subsets cover the universe.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Set-cover instances.** A set-cover instance is a triple $(n, C, K)$ consisting of a natural
number $n$, the size of the universe, a finite list $C$ of finite lists of natural numbers, the
subsets, and a natural number $K$, the bound. -/
abbrev SetCoverInstance := ℕ × List (List ℕ) × ℕ

/-- **Well-formed set-cover instances.** A set-cover instance $(n, C, K)$ is well formed when every
list $s$ in $C$ has no repeated entries and every entry of $s$ is less than $n$, that is, each
member of $C$ lists the elements of a subset of $\{0, \dots, n - 1\}$ without repetition. -/
def WellFormed (i : SetCoverInstance) : Prop :=
  ∀ s ∈ i.2.1, s.Nodup ∧ ∀ x ∈ s, x < i.1

/-- **Feasible set-cover instances.** A set-cover instance $(n, C, K)$ is feasible when there is a
sublist $D$ of $C$ (a list obtained from $C$ by deleting entries while keeping their order) with
at most $K$ entries such that every natural number $x < n$ belongs to some list in $D$. -/
def SetCoverFeasible
    (i : SetCoverInstance) : Prop :=
  ∃ sub : List (List ℕ), sub.Sublist i.2.1 ∧ sub.length ≤ i.2.2 ∧
    ∀ x < i.1, ∃ s ∈ sub, x ∈ s

open Classical in
/-- **The SET COVER decision problem.** SET COVER is the decision problem that accepts a bitstring
$x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a set-cover instance
$(n, C, K)$ that is both well formed and feasible: every list in $C$ has no repeated entries and
only entries less than $n$, and some sublist of $C$ with at most $K$ entries contains every natural
number $y < n$ in one of its lists. Bitstrings that do not decode to a set-cover instance are
rejected. -/
noncomputable def setCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetCoverInstance) x with
  | some i => decide (WellFormed i ∧ SetCoverFeasible i)
  | none => false

/-- **SET COVER is NP-complete.** The SET COVER decision problem lies in NP, and every decision
problem $L$ in NP has a polynomial-time many-one reduction to SET COVER.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), SET COVER; R. M. Karp, "Reducibility among combinatorial problems"
(1972). -/
public theorem_wanted setCover_npComplete :
    setCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L setCoverDec

end MetaMathlibExt.Complexity.NPComplete.SetCover
