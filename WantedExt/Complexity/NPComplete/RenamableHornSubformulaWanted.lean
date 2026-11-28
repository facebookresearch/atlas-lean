/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RENAMABLE HORN SUBFORMULA is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM RENAMABLE HORN SUBFORMULA (decision version);
E. Boros, "Maximum renamable Horn sub-CNFs", Discrete Appl. Math. 96-97 (1999), 29-40,
doi:10.1016/S0166-218X(99)00031-1, Sections 1-2 (definitions; NP-hard because on CNFs whose
clauses all have two literals the problem is equivalent to MAX-2-SAT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RenamableHornSubformulaDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RenamableHornSubformula

open Cslib.Logic.LegacyPL Cslib.Algorithms.SAT.Horn

/-!
# RENAMABLE HORN SUBFORMULA is NP-complete

INSTANCE: a set `U` of variables, a collection `C` of clauses of at most `3` literals over `U`,
and a positive integer `K`.
QUESTION: is there a renamable Horn subformula `C' ⊆ C`, that is, a subset `C'` for which some
`S ⊆ U` makes `C'` a Horn formula after switching the literals in `S ∪ S̄`, with `|C'| ≥ K`?

Following Boros, a clause is a set of literals and a CNF is a family (a set) of clauses;
switching `u` and `ū` replaces every occurrence of `u` by `ū` and every occurrence of `ū` by
`u`, and a Horn CNF has at most one positive literal in each clause
(`Cslib.Algorithms.SAT.Horn.IsHorn`). Here `U = {0, …, n - 1}`, a literal is a pair
`(variable, polarity)` (`Cslib.Logic.LegacyPL.CNF`), a clause is a duplicate-free list of at most
`3` literals, and `C` is a list of clauses no two of which have the same set of literals. The subset
`C'` is a sublist of `C`, so `C'.length = |C'|`. The switching set `S` is given by its indicator
`S : ℕ → Bool`; its values at indices `≥ n` are irrelevant, since no literal uses them.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RENAMABLE HORN SUBFORMULA is NP-complete.** Source: Crescenzi and Kann, MAXIMUM RENAMABLE HORN
SUBFORMULA; Boros (1999). -/
public theorem_wanted renamableHornSubformula_npComplete :
    renamableHornSubformulaDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L renamableHornSubformulaDec

end MetaMathlibExt.Complexity.NPComplete.RenamableHornSubformula
