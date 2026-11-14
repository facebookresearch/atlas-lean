/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PROBABILISTIC SATISFIABILITY is NP-complete

Source:
G. Georgakopoulos, D. Kavvadias, and C. H. Papadimitriou, "Probabilistic satisfiability",
Journal of Complexity 4 (1988), 1-11, doi:10.1016/0885-064X(88)90006-4;
M. Finger and G. De Bona, "A logic based algorithm for solving probabilistic satisfiability",
Advances in Artificial Intelligence (IBERAMIA 2010), Lecture Notes in Computer Science, 453-462,
doi:10.1007/978-3-642-16952-6_46, Section 2 (the problem, Proposition 1 of Georgakopoulos et al.,
and NP-completeness).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Logics.Propositional.CNF.Semantics
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ProbabilisticSatisfiability

/-!
# PROBABILISTIC SATISFIABILITY is NP-complete

INSTANCE: clauses `C₁, …, Cₘ` over the variables `x₁, …, xₙ` and rationals `p₁, …, pₘ` in
`[0, 1]`.
QUESTION: is there a probability distribution `π` on the `2ⁿ` truth assignments (valuations) of
`x₁, …, xₙ` under which each clause `Cᵢ` holds with probability exactly `pᵢ`, i.e.,
`P_π(Cᵢ) = Σ {π(v) | v(Cᵢ) = 1} = pᵢ` (Finger and De Bona, Section 2)?

Georgakopoulos, Kavvadias and Papadimitriou show that a satisfiable instance has a distribution
supported on at most `m + 1` assignments, which gives membership in NP, and that the problem is
NP-hard, even for clauses of at most two literals; SAT is the special case where every `pᵢ = 1`.

Clauses are `Cslib.Logic.PL.CNFClause`s, lists of literals `(variable, polarity)`; the variables
are `0, …, n - 1`, and an assignment `v : Fin n → Bool` is read on all variables by `extend`. A
distribution is a nonnegative real function on assignments summing to `1`. A probability
`pᵢ = aᵢ / bᵢ` is given as two naturals with `bᵢ > 0` and `aᵢ ≤ bᵢ`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of variables, and the clauses `Cᵢ` with their probabilities
`pᵢ = aᵢ / bᵢ`, given as `(aᵢ, bᵢ)`. -/
abbrev ProbabilisticSatisfiabilityInstance := ℕ × List (Cslib.Logic.PL.CNFClause × (ℕ × ℕ))

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
noncomputable def prob {n : ℕ} (π : (Fin n → Bool) → ℝ) (C : Cslib.Logic.PL.CNFClause) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v => Cslib.Logic.PL.CNFClause.Satisfies (extend v) C), π v

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

/-- **PROBABILISTIC SATISFIABILITY is NP-complete.** Source: Georgakopoulos, Kavvadias and
Papadimitriou (1988); Finger and De Bona (2010), Section 2. -/
public theorem_wanted probabilisticSatisfiability_npComplete :
    probabilisticSatisfiabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L probabilisticSatisfiabilityDec

end MetaMathlibExt.Complexity.NPComplete.ProbabilisticSatisfiability
