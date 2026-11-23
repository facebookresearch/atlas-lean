/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM TEST SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MINIMUM TEST COLLECTION;
A. De Bonis, L. Gargano, and U. Vaccaro, "Generalized framework for test set problems" (1997).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumTestSet

/-!
# MINIMUM TEST SET is NP-complete

A universe of size `n`, a list of subsets (tests), and a bound `K`. The question is whether at
most `K` tests distinguish every pair of universe elements: for distinct elements `a, b`, some
chosen test contains exactly one of them.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Minimum test set instance.** An instance of MINIMUM TEST SET is a triple $(n, C, K)$ of a
natural number $n$ (the number of elements), a finite list $C$ of finite lists of natural numbers
(the tests) and a natural number $K$ (the bound). -/
abbrev MinimumTestSetInstance := ℕ × List (List ℕ) × ℕ

/-- **Well-formed minimum test set instance.** An instance $(n, C, K)$ of MINIMUM TEST SET is well
formed when every test in the list $C$ is a list of numbers below $n$ without repeated entries,
so that each test lists a subset of $\{0, \dots, n-1\}$, each element once. -/
def WellFormed (i : MinimumTestSetInstance) : Prop :=
  ∀ s ∈ i.2.1, s.Nodup ∧ ∀ x ∈ s, x < i.1

/-- **Feasible minimum test set instance.** An instance $(n, C, K)$ of MINIMUM TEST SET is feasible
when some sublist $T$ of $C$ (obtained by deleting entries of $C$) has length at most $K$ and
distinguishes every pair: for all distinct $a, b < n$ some test in $T$ contains exactly one of
$a$ and $b$. -/
def MinimumTestSetFeasible
    (i : MinimumTestSetInstance) : Prop :=
  ∃ T : List (List ℕ), T.Sublist i.2.1 ∧ T.length ≤ i.2.2 ∧
    ∀ a < i.1, ∀ b < i.1, a ≠ b →
      ∃ s ∈ T, (a ∈ s ∧ b ∉ s) ∨ (a ∉ s ∧ b ∈ s)

open Classical in
/-- **The MINIMUM TEST SET decision problem.** It accepts a bitstring $x$ exactly when $x$ decodes,
under the canonical bitstring encoding, to a triple $(n, C, K)$ of a natural number $n$, a list
$C$ of lists of natural numbers (the tests) and a natural number $K$ with the following
properties: every test is a list of numbers below $n$ without repeated entries, and some sublist
$T$ of $C$, obtained by deleting entries of $C$, has length at most $K$ and distinguishes every
pair, that is, for all distinct $a, b < n$ some test in $T$ contains exactly one of $a$ and $b$.
Bitstrings that do not decode are rejected. -/
noncomputable def minimumTestSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumTestSetInstance) x with
  | some i => decide (WellFormed i ∧ MinimumTestSetFeasible i)
  | none => false

/-- **MINIMUM TEST SET is NP-complete.** The MINIMUM TEST SET decision problem lies in NP, and
every decision problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), MINIMUM TEST COLLECTION; A. De Bonis, L. Gargano, and U. Vaccaro,
"Generalized framework for test set problems" (1997). -/
public theorem_wanted minimumTestSet_npComplete :
    minimumTestSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumTestSetDec

end MetaMathlibExt.Complexity.NPComplete.MinimumTestSet
