/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SMALLEST GRAMMAR is NP-complete

Source:
M. Charikar, E. Lehman, D. Liu, R. Panigrahy, M. Prabhakaran, A. Sahai, and A. Shelat, "The
smallest grammar problem", IEEE Transactions on Information Theory 51 (2005), 2554-2576,
doi:10.1109/TIT.2005.850116, Sections I, IV-A and V-A;
J. A. Storer and T. G. Szymanski, "Data compression via textual substitution", Journal of the
ACM 29 (1982), 928-951, doi:10.1145/322344.322346.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Computability.ContextFreeGrammar

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SmallestGrammar

/-!
# SMALLEST GRAMMAR is NP-complete

INSTANCE: a string `w` over an alphabet `Σ` and a nonnegative integer `K`.
QUESTION: is there a context-free grammar that generates exactly the string `w` (its language is
`{w}`) whose size, the total number of symbols on the right sides of all rules, is at most `K`?

This is the decision version of the smallest grammar problem of Charikar et al., who state it in
Section I ("What is the smallest context-free grammar that generates exactly one given string?
... The size of a grammar is defined to be the total number of symbols on the right sides of all
rules ... the decision version of this problem is NP-complete") and prove that it cannot be
approximated within a small constant factor unless P = NP (Section V-A, Theorem 1, by a
reduction from vertex cover based on Storer and Szymanski). A grammar of size at most `K` for
`w`, written with one rule per nonterminal and acyclic as in their Section IV-A, is a short
certificate.

Grammars are Mathlib's `ContextFreeGrammar ℕ` (terminals `ℕ`, any type of nonterminals, a
`Finset` of rules), and the size of a grammar is the sum of the lengths of the right sides of its
rules. Charikar et al. consider grammars with exactly one rule per nonterminal and no cycles; a
smallest grammar whose language is `{w}` can always be brought to that form without growing (every
useful nonterminal generates a single string, so one rule each suffices), so both readings ask
the same question. The string is a list of symbols `ℕ` and `K` uses the canonical binary
encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the string `w` and the bound `K`. -/
abbrev SmallestGrammarInstance := List ℕ × ℕ

/-- The size of a grammar: the total number of symbols on the right sides of all its rules. -/
def grammarSize (g : ContextFreeGrammar ℕ) : ℕ :=
  ∑ r ∈ g.rules, r.output.length

/-- Some context-free grammar of size at most `K` generates exactly the string `w`. -/
def SmallestGrammarFeasible (i : SmallestGrammarInstance) : Prop :=
  ∃ g : ContextFreeGrammar ℕ, g.language = {i.1} ∧ grammarSize g ≤ i.2

open Classical in
/-- SMALLEST GRAMMAR as a decision problem over bitstrings. -/
noncomputable def smallestGrammarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SmallestGrammarInstance) x with
  | some i => decide (SmallestGrammarFeasible i)
  | none => false

/-- **SMALLEST GRAMMAR is NP-complete.** Source: Charikar, Lehman, Liu, Panigrahy, Prabhakaran,
Sahai, and Shelat (2005); Storer and Szymanski (1982). -/
public theorem_wanted smallestGrammar_npComplete :
    smallestGrammarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L smallestGrammarDec

end MetaMathlibExt.Complexity.NPComplete.SmallestGrammar
