/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMAL DELETE-FREE PLANNING is NP-complete

Source:
T. Bylander, "The computational complexity of propositional STRIPS planning", Artificial
Intelligence 69 (1994), 165-204, doi:10.1016/0004-3702(94)90081-7;
J. Hoffmann and B. Nebel, "The FF planning system: fast plan generation through heuristic
search", Journal of Artificial Intelligence Research 14 (2001), 253-302, doi:10.1613/jair.855,
Section 3 (STRIPS actions, relaxed planning tasks without delete lists, plans) and Section 4
(computing the optimal length of such a plan is NP-hard, Bylander 1994).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.OptimalDeleteFreePlanningDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimalDeleteFreePlanning

/-!
# OPTIMAL DELETE-FREE PLANNING is NP-complete

INSTANCE: a propositional STRIPS planning task `(O, I, G)` whose actions have no delete lists,
i.e., a set `O` of actions `o = (pre(o), add(o))` with preconditions `pre(o)` and add list
`add(o)`, an initial state `I` and goals `G` (all sets of atoms), and a natural number `K`.
QUESTION: is there a plan of at most `K` actions, i.e., a sequence `⟨o₁, …, oₙ⟩` of actions in
`O` with `n ≤ K` and `G ⊆ Result(I, ⟨o₁, …, oₙ⟩)`?

A state is a finite set of atoms. Applying an action `o` to a state `S` gives `S ∪ add(o)` when
`pre(o) ⊆ S` and is undefined otherwise (there is no delete list to remove); a sequence of actions
is applied from left to right, and is undefined as soon as one action is inapplicable
(Hoffmann and Nebel, Definitions 1-5, with every delete list empty). Atoms are natural numbers,
sets of atoms are given as lists, and a plan is a list of positions in the action list (an action
may occur several times). Every instance is well formed. Plans without deletes can always be
shortened to at most one action per atom, so a short witness exists; the problem is the
NP-complete decision version of computing the optimal relaxed plan length `h⁺`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **OPTIMAL DELETE-FREE PLANNING is NP-complete.** Source: Bylander (1994); Hoffmann and Nebel
(2001). -/
public theorem_wanted optimalDeleteFreePlanning_npComplete :
    optimalDeleteFreePlanningDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L optimalDeleteFreePlanningDec

end MetaMathlibExt.Complexity.NPComplete.OptimalDeleteFreePlanning
