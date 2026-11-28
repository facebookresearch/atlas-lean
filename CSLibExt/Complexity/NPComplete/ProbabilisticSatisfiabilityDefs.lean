/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PROBABILISTIC SATISFIABILITY: definitions

Source:
G. Georgakopoulos, D. Kavvadias, and C. H. Papadimitriou, "Probabilistic satisfiability",
Journal of Complexity 4 (1988), 1-11, doi:10.1016/0885-064X(88)90006-4;
M. Finger and G. De Bona, "A logic based algorithm for solving probabilistic satisfiability",
Advances in Artificial Intelligence (IBERAMIA 2010), Lecture Notes in Computer Science, 453-462,
doi:10.1007/978-3-642-16952-6_46, Section 2 (the problem, Proposition 1 of Georgakopoulos et al.,
and NP-completeness).
-/
module

public import CSLibExt.Logics.Propositional.CNF.Semantics
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ProbabilisticSatisfiability

/-- An instance: the number `n` of variables, and the clauses `Cᵢ` with their probabilities
`pᵢ = aᵢ / bᵢ`, given as `(aᵢ, bᵢ)`. -/
abbrev ProbabilisticSatisfiabilityInstance := ℕ × List (Cslib.Logic.LegacyPL.CNFClause × (ℕ × ℕ))

/-- Well-formedness: every clause uses the variables `0, …, n - 1`, and every probability
`aᵢ / bᵢ` has `bᵢ > 0` and lies in `[0, 1]`. -/
def WellFormed (i : ProbabilisticSatisfiabilityInstance) : Prop :=
  ∀ e ∈ i.2, (∀ l ∈ e.1, l.1 < i.1) ∧ 0 < e.2.2 ∧ e.2.1 ≤ e.2.2

/-- A truth assignment to the variables `0, …, n - 1`, read on all variables (`false` beyond
`n`, where no clause of a well-formed instance looks). -/
def extend {n : ℕ} (v : Fin n → Bool) : ℕ → Bool :=
  fun x => if h : x < n then v ⟨x, h⟩ else false

open Classical in
/-- `P_π(C)`: the total probability of the assignments that satisfy the clause `C`. -/
noncomputable def prob {n : ℕ} (π : (Fin n → Bool) → ℝ) (C : Cslib.Logic.LegacyPL.CNFClause) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v => Cslib.Logic.LegacyPL.CNFClause.Satisfies (extend v) C), π v

/-- Some probability distribution on the assignments gives every clause `Cᵢ` probability
exactly `pᵢ`. -/
def ProbabilisticSatisfiabilityFeasible (i : ProbabilisticSatisfiabilityInstance) : Prop :=
  ∃ π : (Fin i.1 → Bool) → ℝ, (∀ v, 0 ≤ π v) ∧ ∑ v, π v = 1 ∧
    ∀ e ∈ i.2, prob π e.1 = (e.2.1 : ℝ) / e.2.2

open Classical in
/-- PROBABILISTIC SATISFIABILITY as a decision problem over bitstrings. -/
noncomputable def probabilisticSatisfiabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ProbabilisticSatisfiabilityInstance) x with
  | some i => decide (WellFormed i ∧ ProbabilisticSatisfiabilityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ProbabilisticSatisfiability
