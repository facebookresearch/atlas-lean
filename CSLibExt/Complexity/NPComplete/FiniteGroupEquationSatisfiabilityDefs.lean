/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EQUATION SATISFIABILITY over a fixed finite nonsolvable group: definitions

Source:
M. Goldmann and A. Russell, "The complexity of solving equations over finite groups",
Information and Computation 178 (2002), 253-262, doi:10.1006/inco.2002.3173.
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.GroupTheory.Solvable
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FiniteGroupEquationSatisfiability

/-- An instance: the word `w` as a list of tokens `(kind, index)`. -/
abbrev FiniteGroupEquationSatisfiabilityInstance := List (ℕ × ℕ)

/-- The value of a token under the numbering `e` of the constants and the assignment `σ` of
the variables: `(0, c)` is the constant `e c`, `(1, x)` is `σ x`, and `(2, x)` is `(σ x)⁻¹`.
Other tokens are excluded by `WellFormed`. -/
def tokenValue {G : Type*} [Group G] {n : ℕ} (e : Fin n ≃ G) (σ : ℕ → G) : ℕ × ℕ → G
  | (0, c) => if h : c < n then e ⟨c, h⟩ else 1
  | (1, x) => σ x
  | (_, x) => (σ x)⁻¹

/-- Well-formedness of an instance: every token is a constant, a variable or an inverted
variable, and every constant token names one of the `n` elements of `G`. -/
def WellFormed (n : ℕ) (i : FiniteGroupEquationSatisfiabilityInstance) : Prop :=
  ∀ t ∈ i, t.1 ≤ 2 ∧ (t.1 = 0 → t.2 < n)

/-- Some assignment of elements of `G` to the variables makes the word evaluate to `1`. -/
def FiniteGroupEquationSatisfiabilityFeasible {G : Type*} [Group G] {n : ℕ} (e : Fin n ≃ G)
    (i : FiniteGroupEquationSatisfiabilityInstance) : Prop :=
  ∃ σ : ℕ → G, (i.map (tokenValue e σ)).prod = 1

open Classical in
/-- EQUATION SATISFIABILITY over `G`, with the constants numbered by `e`, as a decision problem
over bitstrings. -/
noncomputable def finiteGroupEquationSatisfiabilityDec {G : Type*} [Group G] {n : ℕ}
    (e : Fin n ≃ G) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FiniteGroupEquationSatisfiabilityInstance) x with
  | some i => decide (WellFormed n i ∧ FiniteGroupEquationSatisfiabilityFeasible e i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FiniteGroupEquationSatisfiability
