/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED STRIPS PLANNING (plan length in unary) is NP-complete

Source:
T. Bylander, "The computational complexity of propositional STRIPS planning", Artificial
Intelligence 69 (1994), 165-204, doi:10.1016/0004-3702(94)90081-7, Section 2.1 (propositional
STRIPS planning, `PLANMIN`) and Theorem 4.2 (`3SAT` reduces to `PLANMIN` with bound
`k = 2m + n`);
D. Speck, M. Hecher, D. Gnad, J. K. Fichte, and A. B. Corrêa, "Counting and reasoning with
plans", Proceedings of the AAAI Conference on Artificial Intelligence 39 (2025),
doi:10.1609/aaai.v39i25.34871; extended version arXiv:2502.00145, Section 2 (bounded plan
existence with a polynomially bounded plan length is NP-complete, Bylander 1994).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BoundedStripsPlanningDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedStripsPlanning

/-!
# BOUNDED STRIPS PLANNING (plan length in unary) is NP-complete

INSTANCE: a propositional STRIPS planning instance `⟨P, O, I, G⟩` (Bylander, Section 2.1): a
finite set `P` of conditions; a finite set `O` of operators `Pre ⇒ Post`, where `Pre` is a
satisfiable conjunction of positive and negative conditions (the positive preconditions `o₊` and
the negative preconditions `o₋`) and `Post` is a satisfiable conjunction of positive and negative
conditions (the positive postconditions `o⁺`, the add list, and the negative postconditions `o⁻`,
the delete list); an initial state `I ⊆ P`; and goals `G`, a satisfiable conjunction of positive
goals `G₊` and negative goals `G₋`. Also a natural number `k`, written in unary.
QUESTION: is there a solution of `k` operators or less, i.e., a finite sequence
`(o₁, …, oₙ)` of operators of `O` with `n ≤ k` such that `Result(I, (o₁, …, oₙ))` is a goal
state (`G₊ ⊆ S` and `G₋ ∩ S = ∅`)?

`Result(S, (o)) = (S ∪ o⁺) \ o⁻` if `o₊ ⊆ S` and `o₋ ∩ S = ∅`, and `S` otherwise (an
operator whose preconditions fail has no effect); a sequence is applied from left to right, and an
operator may appear several times. This is Bylander's `PLANMIN` with `k` given in unary. It is in
NP because a solution of at most `k` operators is a certificate of size polynomial in the unary
`k`; it is NP-hard because Bylander's reduction from `3SAT` (Theorem 4.2) produces the bound
`k = 2m + n`, polynomial in the formula. With `k` in binary the problem is PSPACE-complete
(Bylander, Theorem 4.1).

The conditions are `P = {0, …, N - 1}`; sets of conditions are lists. The bound `k` is the length
of a list `[true, …, true]` (`k` written in unary). Bylander only requires that "`k` is given as
part of the input" (Sections 2.1 and 4), so `k = 0` is an instance: it asks whether `I` is
itself a goal state.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BOUNDED STRIPS PLANNING with the plan length in unary is NP-complete.** Source: Bylander
(1994), Section 2.1 and Theorem 4.2; Speck, Hecher, Gnad, Fichte, and Corrêa (2025), Section 2. -/
public theorem_wanted boundedStripsPlanning_npComplete :
    boundedStripsPlanningDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L boundedStripsPlanningDec

end MetaMathlibExt.Complexity.NPComplete.BoundedStripsPlanning
