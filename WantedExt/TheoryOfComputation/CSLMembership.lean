/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Languages.ContextSensitive.Basic
public import CSLibExt.Computability.Machines.Turing.MultiTape.TimeSpace
public import Mathlib.Computability.RE

@[expose] public section

set_option autoImplicit false

namespace Cslib.CSLMembershipWanted

/-- **Context-sensitive membership is decidable, in PSPACE**: for every
grammar `g` over `Bool` with `IsContextSensitive g`, membership in its
language is a computable predicate, and the language lies in
deterministic polynomial space on the multi-tape model. `CSGrammar`
itself is the unrestricted grammar structure, so the
context-sensitivity hypothesis is essential: without it the claim
would cover shrinking (type-0) grammars, whose membership need not be
decidable. Given the hypothesis, membership is decidable because a
context-sensitive derivation of a word of length `n` never needs a
sentential form longer than `n` (productions do not shrink), so the
finitely many sentential forms up to that length can be enumerated;
the PSPACE bound is Savitch's simulation of the nondeterministic
linear-space search. Stated over `Bool` so the language is directly a
`Set (List Bool)` for the multi-tape space class. Source: Sipser,
*Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013,
§5.1 (Theorem 5.9, decidability of `A_LBA`) and §8.2 (Savitch's theorem,
`NPSPACE = PSPACE`); Hopcroft-Motwani-Ullman, *Introduction to Automata
Theory, Languages, and Computation*, 3rd ed., Pearson, 2007, §11.1. -/
theorem_wanted csl_membership_decidable_pspace :
  ∀ {N : Type*} (g : Cslib.Language.CSGrammar Bool N),
    Cslib.Language.IsContextSensitive g →
    ComputablePred (fun w : List Bool ↦ w ∈ Cslib.Language.language g) ∧
      Cslib.Language.language g ∈ Cslib.Turing.MultiTapeTM.Classes.PSPACE

end Cslib.CSLMembershipWanted
