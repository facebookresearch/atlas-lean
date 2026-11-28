/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STABLE MODEL EXISTENCE is NP-complete

Source:
W. Marek and M. Truszczyński, "Autoepistemic logic", Journal of the ACM 38 (1991), 588-619,
doi:10.1145/116825.116836 ("it is proven that the problem of existence of stable models is
NP-complete"); stable models: M. Gelfond and V. Lifschitz, "The stable model semantics for logic
programming", Logic Programming: Proceedings of the Fifth International Conference and Symposium
(ICLP/SLP 1988), MIT Press, 1070-1080.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.StableModelExistenceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StableModelExistence

open Cslib.Logic.LegacyPL (CNF)

/-!
# STABLE MODEL EXISTENCE is NP-complete

INSTANCE: a finite propositional normal logic program `P`, a finite set of rules
`a ← b₁, …, bₖ, not c₁, …, not cₗ` (`k, l ≥ 0`) over a set of atoms. QUESTION: does `P` have a
stable model?

Following Gelfond and Lifschitz, the reduct `P^M` of `P` with respect to a set `M` of atoms
deletes every rule with some `cⱼ ∈ M` and drops the negative bodies `not c₁, …, not cₗ` of the
remaining rules; `M` is a stable model of `P` when `M` is the least model of the definite program
`P^M`. A definite rule `a ← b₁, …, bₖ` is the Horn clause `a ∨ ¬b₁ ∨ … ∨ ¬bₖ`, and the least model
of `P^M` is `Cslib.Algorithms.SAT.Horn.close (P^M) ∅`, the least set of atoms containing `a`
whenever it contains `b₁, …, bₖ` for a rule `a ← b₁, …, bₖ` of `P^M` (`Horn.subset_close`,
`Horn.derive_close_subset`, `Horn.close_subset`). Atoms are natural numbers; every list of rules
is a program, so there is no well-formedness condition.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STABLE MODEL EXISTENCE is NP-complete.** Source: Marek and Truszczyński (1991). -/
public theorem_wanted stableModelExistence_npComplete :
    stableModelExistenceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L stableModelExistenceDec

end MetaMathlibExt.Complexity.NPComplete.StableModelExistence
