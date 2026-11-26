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
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Rat
public import WantedExt.Complexity.NPComplete.QuadraticProgrammingWanted

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

/-- The value `a / d` of a probability given as `(a, d)`. -/
def probVal (q : ℕ × ℕ) : ℚ := (q.1 : ℚ) / q.2

/-- The data of one agent: the prior (one probability per type) and the utility table (one row
per type, one entry per outcome). -/
abbrev AgentData := List (ℕ × ℕ) × List (List RatCode)

/-- An instance: the number of outcomes `m`, the data of agents 1 and 2, the objective table
`g` (indexed by `θ₁`, `θ₂`, outcome), and the goal `G`. -/
abbrev DeterministicMechanismDesignDominantStrategiesInstance :=
  ℕ × AgentData × AgentData × List (List (List RatCode)) × RatCode

/-- The listed weight `pᵢ(θ)` of type `θ` (`0` when missing), a prior probability when the
agent's weights sum to `1`. -/
def prior (a : AgentData) (θ : ℕ) : ℚ := probVal (a.1.getD θ (0, 1))

/-- The utility `uᵢ(θ, o)` of an agent of type `θ` for outcome `o`. -/
def utility (a : AgentData) (θ o : ℕ) : ℚ := ratVal ((a.2.getD θ []).getD o ((0, 0), 1))

/-- The objective value `g(θ₁, θ₂, o)`. -/
def objective (i : DeterministicMechanismDesignDominantStrategiesInstance) (θ₁ θ₂ o : ℕ) : ℚ :=
  ratVal (((i.2.2.2.1.getD θ₁ []).getD θ₂ []).getD o ((0, 0), 1))

/-- Well-formedness of one agent's data for `m` outcomes: positive denominators, prior
probabilities summing to `1`, and one utility row of `m` entries per type. -/
def AgentWellFormed (m : ℕ) (a : AgentData) : Prop :=
  (∀ q ∈ a.1, 0 < q.2) ∧ (a.1.map probVal).sum = 1 ∧ a.2.length = a.1.length ∧
    ∀ row ∈ a.2, row.length = m ∧ ∀ r ∈ row, 0 < r.2

/-- Well-formedness of an instance: both agents' data are well formed, the objective table has
one entry per type vector and outcome, and every denominator is positive. -/
def WellFormed (i : DeterministicMechanismDesignDominantStrategiesInstance) : Prop :=
  AgentWellFormed i.1 i.2.1 ∧ AgentWellFormed i.1 i.2.2.1 ∧
    i.2.2.2.1.length = i.2.1.1.length ∧
    (∀ row ∈ i.2.2.2.1, row.length = i.2.2.1.1.length ∧
      ∀ col ∈ row, col.length = i.1 ∧ ∀ r ∈ col, 0 < r.2) ∧
    0 < i.2.2.2.2.2

/-- A deterministic mechanism: an outcome for every vector of reported types. -/
abbrev Mechanism (i : DeterministicMechanismDesignDominantStrategiesInstance) :=
  Fin i.2.1.1.length → Fin i.2.2.1.1.length → Fin i.1

/-- The mechanism implements its outcome function in dominant strategies: for each agent,
reporting the true type is optimal whatever type the other agent reports. -/
def IsDominantStrategyImplementation
    (i : DeterministicMechanismDesignDominantStrategiesInstance) (o : Mechanism i) : Prop :=
  (∀ (θ₁ θ₁' : Fin i.2.1.1.length) (θ₂ : Fin i.2.2.1.1.length),
      utility i.2.1 θ₁ (o θ₁' θ₂) ≤ utility i.2.1 θ₁ (o θ₁ θ₂)) ∧
    ∀ (θ₁ : Fin i.2.1.1.length) (θ₂ θ₂' : Fin i.2.2.1.1.length),
      utility i.2.2.1 θ₂ (o θ₁ θ₂') ≤ utility i.2.2.1 θ₂ (o θ₁ θ₂)

/-- The prior-weighted sum of `g(θ₁, θ₂, o(θ₁, θ₂))`, the expectation under the independent
priors when both priors are probability distributions. -/
def expectedObjective (i : DeterministicMechanismDesignDominantStrategiesInstance)
    (o : Mechanism i) : ℚ :=
  ∑ θ₁ : Fin i.2.1.1.length, ∑ θ₂ : Fin i.2.2.1.1.length,
    prior i.2.1 θ₁ * prior i.2.2.1 θ₂ * objective i θ₁ θ₂ (o θ₁ θ₂)

/-- Some deterministic mechanism implements its outcome function in dominant strategies and
attains the goal: `E[g] ≥ G`. -/
def DeterministicMechanismDesignDominantStrategiesFeasible
    (i : DeterministicMechanismDesignDominantStrategiesInstance) : Prop :=
  ∃ o : Mechanism i, IsDominantStrategyImplementation i o ∧
    ratVal i.2.2.2.2 ≤ expectedObjective i o

open Classical in
/-- DETERMINISTIC MECHANISM DESIGN WITH DOMINANT STRATEGIES (two agents) as a decision problem
over bitstrings. -/
noncomputable def deterministicMechanismDesignDominantStrategiesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DeterministicMechanismDesignDominantStrategiesInstance) x with
  | some i => decide (WellFormed i ∧ DeterministicMechanismDesignDominantStrategiesFeasible i)
  | none => false

/-- **DETERMINISTIC MECHANISM DESIGN WITH DOMINANT STRATEGIES (two agents) is NP-complete.**
Source: Conitzer and Sandholm (2002), Theorem 1. -/
public theorem_wanted deterministicMechanismDesignDominantStrategies_npComplete :
    deterministicMechanismDesignDominantStrategiesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L deterministicMechanismDesignDominantStrategiesDec

end MetaMathlibExt.Complexity.NPComplete.DeterministicMechanismDesignDominantStrategies
