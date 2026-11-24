/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXACT COVER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), EXACT COVER; R. M. Karp,
"Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExactCover

/-!
# EXACT COVER is NP-complete

A universe of size `n` (elements `0, …, n - 1`) and a list of subsets. The question is whether
some subcollection covers every element exactly once.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of EXACT COVER.** An instance of EXACT COVER is a pair $(n, C)$ of a natural
number $n$, the size of the universe $\{0, \dots, n - 1\}$, and a finite list $C$ of finite lists
of natural numbers, the candidate subsets. That each entry of $C$ lists distinct elements of the
universe is required by well-formedness, not by the type of instances. -/
abbrev ExactCoverInstance := ℕ × List (List ℕ)

/-- **Well-formed EXACT COVER instances.** An instance $(n, C)$ of EXACT COVER is well formed
when every entry of $C$ is a list of pairwise distinct natural numbers, each less than $n$. -/
def WellFormed (i : ExactCoverInstance) : Prop :=
  ∀ s ∈ i.2, s.Nodup ∧ ∀ x ∈ s, x < i.1

/-- **Feasible EXACT COVER instances.** An instance $(n, C)$ of EXACT COVER is feasible when $C$
has a sublist $S$, obtained by deleting some entries of $C$, such that for every natural number
$x < n$ there is exactly one list that occurs in $S$ and contains $x$. -/
def ExactCoverFeasible
    (i : ExactCoverInstance) : Prop :=
  ∃ sub : List (List ℕ), sub.Sublist i.2 ∧
    ∀ x < i.1, ∃! s ∈ sub, x ∈ s

open Classical in
/-- **EXACT COVER as a decision problem.** The decision problem EXACT COVER accepts a bitstring
$x$ exactly when $x$ decodes, under the canonical bitstring encoding of pairs of a natural number
and a list of lists of natural numbers, to an instance of EXACT COVER that is well formed and
feasible; bitstrings that do not decode are rejected. -/
noncomputable def exactCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExactCoverInstance) x with
  | some i => decide (WellFormed i ∧ ExactCoverFeasible i)
  | none => false

/-- **EXACT COVER is NP-complete.** The decision problem EXACT COVER is in NP, and every decision
problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), EXACT COVER; R. M. Karp, "Reducibility among combinatorial
problems" (1972). -/
public theorem_wanted exactCover_npComplete :
    exactCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L exactCoverDec

end MetaMathlibExt.Complexity.NPComplete.ExactCover
