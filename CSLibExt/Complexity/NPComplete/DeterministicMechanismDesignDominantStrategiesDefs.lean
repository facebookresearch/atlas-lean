/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DETERMINISTIC MECHANISM DESIGN WITH DOMINANT STRATEGIES (two agents): definitions

Source:
V. Conitzer and T. Sandholm, "Complexity of mechanism design", Proceedings of the Eighteenth
Conference on Uncertainty in Artificial Intelligence (UAI 2002), 103-110,
arXiv:cs/0205075, Definitions 1-3 and 5, Theorem 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Rat
public import CSLibExt.Complexity.NPComplete.QuadraticProgrammingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DeterministicMechanismDesignDominantStrategies

open QuadraticProgramming (RatCode ratVal)

/-- The value `a / d` of a probability given as `(a, d)`. -/
def probVal (q : ℕ × ℕ) : ℚ := (q.1 : ℚ) / q.2

/-- The data of one agent: the prior (one probability per type) and the utility table (one row
per type, one entry per outcome). -/
abbrev AgentData := List (ℕ × ℕ) × List (List RatCode)

/-- An instance: the number of outcomes `m`, the data of agents 1 and 2, the objective table
`g` (indexed by `θ₁`, `θ₂`, outcome), and the goal `G`. -/
abbrev DeterministicMechanismDesignDominantStrategiesInstance :=
  ℕ × AgentData × AgentData × List (List (List RatCode)) × RatCode

/-- The prior probability `pᵢ(θ)` of type `θ`. -/
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

/-- The expected objective `E[g(θ₁, θ₂, o(θ₁, θ₂))]` under the independent priors. -/
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

end MetaMathlibExt.Complexity.NPComplete.DeterministicMechanismDesignDominantStrategies
