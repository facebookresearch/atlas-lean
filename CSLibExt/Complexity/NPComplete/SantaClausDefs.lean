/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SANTA CLAUS (MAX-MIN FAIR ALLOCATION): definitions

Source:
I. Bezáková and V. Dani, "Allocating indivisible goods", ACM SIGecom Exchanges 5(3) (2005),
11-18, doi:10.1145/1120680.1120683 (the Max-Min Fairness problem);
B. L. Deuermeyer, D. K. Friesen and M. A. Langston, "Scheduling to maximize the minimum
processor finish time in a multiprocessor system", SIAM Journal on Algebraic and Discrete
Methods 3 (1982), 190-196, doi:10.1137/0603019 (NP-hardness when all agents value the goods
alike).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SantaClaus

/-- An instance: the number `m` of goods, one row `(vᵢ(0), …, vᵢ(m - 1))` of valuations per agent
`i`, and the bound `T`. -/
abbrev SantaClausInstance := ℕ × List (List ℕ) × ℕ

/-- The agents of the instance, `Fin k` for `k` rows. -/
abbrev Agent (inst : SantaClausInstance) : Type := Fin inst.2.1.length

/-- The value `vᵢ(j)` of good `j` for agent `i`. -/
def value (inst : SantaClausInstance) (i : Agent inst) (j : Fin inst.1) : ℕ :=
  (inst.2.1.get i).getD j 0

/-- Well-formedness of an instance: there is at least one agent, and every agent's row has one
valuation per good. -/
def WellFormed (inst : SantaClausInstance) : Prop :=
  inst.2.1 ≠ [] ∧ ∀ r ∈ inst.2.1, r.length = inst.1

/-- Some allocation `f` of the goods to the agents gives every agent total value at least `T`. -/
def SantaClausFeasible (inst : SantaClausInstance) : Prop :=
  ∃ f : Fin inst.1 → Agent inst, ∀ i, inst.2.2 ≤ ∑ j ∈ Finset.univ.filter (f · = i), value inst i j

open Classical in
/-- SANTA CLAUS as a decision problem over bitstrings. -/
noncomputable def santaClausDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SantaClausInstance) x with
  | some i => decide (WellFormed i ∧ SantaClausFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SantaClaus
