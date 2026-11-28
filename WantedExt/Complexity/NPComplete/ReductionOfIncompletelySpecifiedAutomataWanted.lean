/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REDUCTION OF INCOMPLETELY SPECIFIED AUTOMATA is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL7] REDUCTION OF
INCOMPLETELY SPECIFIED AUTOMATA;
C. P. Pfleeger, "State reduction in incompletely specified finite-state
machines", IEEE Transactions on Computers C-22 (1973), 1099-1102,
doi:10.1109/T-C.1973.223655.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomataDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomata

/-!
# REDUCTION OF INCOMPLETELY SPECIFIED AUTOMATA is NP-complete

INSTANCE: an incompletely specified deterministic finite state automaton
`A = (Q, Σ, δ, q₀, F)`, whose transition function `δ` maps a subset of `Q × Σ` into `Q`, and a
positive integer `K`. QUESTION: can `δ` be extended to a total function `Q × Σ → Q` so that the
resulting completely specified automaton has an equivalent reduced automaton with `K` or fewer
states?

The states are `Fin n` and the alphabet is `Fin m`. The partial transition function is a list of
entries `((q, a), q')`, read as `δ(q, a) = q'`; `WellFormed` requires the list to be functional.
A completion is a total `d : Fin n → Fin m → Fin n` that agrees with every listed entry; it
gives the Mathlib `DFA` `completion i d q₀`. Two automata are equivalent when they accept the same
language, so the completed automaton has an equivalent reduced (minimum-state) automaton with at
most `K` states exactly when some `DFA` with at most `K` states accepts its language.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **REDUCTION OF INCOMPLETELY SPECIFIED AUTOMATA is NP-complete.** Source: Garey and Johnson
(1979), [AL7]; Pfleeger (1973). -/
public theorem_wanted reductionOfIncompletelySpecifiedAutomata_npComplete :
    reductionOfIncompletelySpecifiedAutomataDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L reductionOfIncompletelySpecifiedAutomataDec

end MetaMathlibExt.Complexity.NPComplete.ReductionOfIncompletelySpecifiedAutomata
