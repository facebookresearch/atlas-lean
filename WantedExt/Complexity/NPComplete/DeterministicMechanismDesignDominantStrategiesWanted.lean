/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DETERMINISTIC MECHANISM DESIGN WITH DOMINANT STRATEGIES (two agents) is NP-complete

Source:
V. Conitzer and T. Sandholm, "Complexity of mechanism design", Proceedings of the Eighteenth
Conference on Uncertainty in Artificial Intelligence (UAI 2002), 103-110,
arXiv:cs/0205075, Definitions 1-3 and 5, Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DeterministicMechanismDesignDominantStrategiesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DeterministicMechanismDesignDominantStrategies

open QuadraticProgramming (RatCode ratVal)

/-!
# DETERMINISTIC MECHANISM DESIGN WITH DOMINANT STRATEGIES (two agents) is NP-complete

INSTANCE: a preference aggregation setting with two agents: a finite set `O` of outcomes and,
for each agent `i ∈ {1, 2}`, a finite set `Θᵢ` of types, a probability distribution `pᵢ` over
`Θᵢ`, and a utility function `uᵢ : Θᵢ × O → ℚ`; an objective function
`g : Θ₁ × Θ₂ × O → ℚ` and a goal `G ∈ ℚ`.
QUESTION: is there a deterministic mechanism `o : Θ₁ × Θ₂ → O` that implements its outcome
function in dominant strategies, i.e. `uᵢ(θᵢ, o(θᵢ, θ₋ᵢ)) ≥ uᵢ(θᵢ, o(θ̂ᵢ, θ₋ᵢ))` for each agent
`i`, all type vectors and every misreport `θ̂ᵢ`, and that attains the goal,
`E[g(θ₁, θ₂, o(θ₁, θ₂))] ≥ G` with the types drawn independently from `p₁` and `p₂`?

This is DETERMINISTIC-MECHANISM-DESIGN (Conitzer and Sandholm, Definition 5) with the dominant
strategy solution concept (Definition 3) and `N = 2` agents. Theorem 1 proves it NP-complete
"even with 2 agents and the social welfare function as the objective function"; its membership
argument is the two-agent one (a mechanism is a table of `|Θ₁| × |Θ₂|` outcomes). Definition 5
has no individual-rationality constraint, so none is stated here. For an unbounded number of
agents the source notes that an outcome function needs exponential space; that version is not
stated here.

Outcomes are `0, ..., m - 1` and the types of agent `i` are `0, ..., |Θᵢ| - 1`, where `|Θᵢ|` is
the length of the prior's list. A rational number is given as `((a, b), d)` with value
`(a - b) / d` and `0 < d` (`QuadraticProgramming.RatCode` and `QuadraticProgramming.ratVal`,
reused from `QuadraticProgrammingWanted`); a probability is given as `(a, d)` with value `a / d` and
`0 < d`. Agent `i`'s utility table has one row of `m` entries per type, and the objective table is
indexed by `θ₁`, then `θ₂`, then the outcome. All numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DETERMINISTIC MECHANISM DESIGN WITH DOMINANT STRATEGIES (two agents) is NP-complete.**
Source: Conitzer and Sandholm (2002), Theorem 1. -/
public theorem_wanted deterministicMechanismDesignDominantStrategies_npComplete :
    deterministicMechanismDesignDominantStrategiesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L deterministicMechanismDesignDominantStrategiesDec

end MetaMathlibExt.Complexity.NPComplete.DeterministicMechanismDesignDominantStrategies
