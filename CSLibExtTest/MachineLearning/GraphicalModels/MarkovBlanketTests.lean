/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.MarkovBlanket
public import CSLibExt.MachineLearning.GraphicalModels.Junctions
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Tests for Markov blankets and the local Markov property

A four-node collider net `0 → 2 ← 1`, `1 → 3` on `Bool`: `X₀`, `X₁` are fair coins,
`X₂ = X₀ ∨ X₁` and `X₃ = X₁`. The Markov blanket of `0` is `{1, 2}` (child `2` and co-parent `1`),
and `X₀ ⫫ X₃ | X₁, X₂`. Removing the co-parent breaks it (Berkson's paradox):
`¬ X₀ ⫫ X₁, X₃ | X₂` and `¬ X₀ ⫫ X₃ | X₂`, at `x = (true, true, true, true)` where
`P(X₀, X₂, X₃) P(X₂) = 1/4 · 3/4 ≠ 1/2 · 1/2 = P(X₀, X₂) P(X₂, X₃)`. The local Markov property at
node `3` gives `X₃ ⫫ X₀, X₂ | X₁`. The joint has zero cells, so the cross-multiplied form of
conditional independence is exercised where conditioning events have probability zero.
-/

@[expose] public section

namespace Cslib.MachineLearning.MarkovBlanketTests

open Cslib.MachineLearning GraphicalModels Junctions MetaMathlibExt.FiniteWeight Finset Convexity

/-- Parents: `pa 2 = {0, 1}`, `pa 3 = {1}`, nodes `0` and `1` are roots. -/
def berkson4Pa : (k : Fin 4) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => ∅
  | ⟨2, _⟩ => {0, 1}
  | ⟨3, _⟩ => {1}
  | ⟨_ + 4, h⟩ => absurd h (by omega)

/-- Tables: fair coins at `0`, `1`; `X₂ = X₀ ∨ X₁`; `X₃ = X₁`. -/
noncomputable def berkson4Cpt : (k : Fin 4) → (berkson4Pa k → Bool) → StdSimplex ℝ Bool
  | ⟨0, _⟩, _ => fairCoin
  | ⟨1, _⟩, _ => fairCoin
  | ⟨2, _⟩, u => StdSimplex.single (u ⟨0, by simp [berkson4Pa]⟩ || u ⟨1, by simp [berkson4Pa]⟩)
  | ⟨3, _⟩, u => StdSimplex.single (u ⟨1, by simp [berkson4Pa]⟩)
  | ⟨_ + 4, h⟩, _ => absurd h (by omega)

/-- The four-node collider net. -/
noncomputable def berkson4 : BayesNet Bool 4 := ⟨berkson4Pa, berkson4Cpt⟩

theorem berkson4_edge {i j : Fin 4} :
    berkson4.Edge i j ↔ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) := by
  change (∃ h : (i : ℕ) < j, (⟨i, h⟩ : Fin j) ∈ berkson4Pa j) ↔ _
  fin_cases i <;> fin_cases j <;> decide

/-- The Markov blanket of `0` is its child `2` and its co-parent `1`. -/
theorem berkson4_markovBlanket_zero : berkson4.markovBlanket 0 = {1, 2} := by
  ext j
  rw [BayesNet.mem_markovBlanket]
  simp only [berkson4_edge, mem_insert, mem_singleton]
  fin_cases j <;> simp

/-- Nonvacuity of the blanket statement: the complement of `{0} ∪ MB(0)` is `{3}`. -/
theorem berkson4_rest_zero : univ \ insert 0 (berkson4.markovBlanket 0) = {3} := by
  rw [berkson4_markovBlanket_zero]
  decide

theorem berkson4_joint (x : Fin 4 → Bool) :
    berkson4.joint x = if x 2 = (x 0 || x 1) ∧ x 3 = x 1 then 1 / 4 else 0 := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_four]
  change fairCoin.weights (x 0) * fairCoin.weights (x 1) *
    (StdSimplex.single (x 0 || x 1)).weights (x 2) * (StdSimplex.single (x 1)).weights (x 3) = _
  simp only [fairCoin_weights, StdSimplex.weights_single, Finsupp.single_apply,
    @eq_comm _ (x 0 || x 1) (x 2), @eq_comm _ (x 1) (x 3)]
  by_cases h2 : x 2 = (x 0 || x 1) <;> by_cases h3 : x 3 = x 1 <;> simp [h2, h3]
  norm_num

private theorem sum_four (f : (Fin 4 → Bool) → ℝ) :
    ∑ x, f x = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, f ![a, b, c, d] := by
  rw [sum_snoc, sum_snoc, sum_snoc, sum_snoc, Fintype.sum_unique]
  refine Fintype.sum_congr _ _ fun a => Fintype.sum_congr _ _ fun b =>
    Fintype.sum_congr _ _ fun c => Fintype.sum_congr _ _ fun d => congrArg f ?_
  funext i
  fin_cases i <;> rfl

/-- **Positive check**: `X₀ ⫫ X₃ | X_{MB(0)}`, the blanket corollary at node `0`. -/
theorem berkson4_condIndep_blanket :
    CondIndep berkson4.joint {0} ↑({3} : Finset (Fin 4)) ↑({1, 2} : Finset (Fin 4)) := by
  have h := berkson4.condIndep_markovBlanket 0
  rwa [berkson4_rest_zero, berkson4_markovBlanket_zero] at h

/-- The blanket event at `x = (true, true, true, true)` has positive probability `1/2`. -/
theorem berkson4_marginal_blanket :
    marginal berkson4.joint ↑({1, 2} : Finset (Fin 4)) ![true, true, true, true] = 1 / 2 := by
  simp only [marginal, sum_filter, sum_four, berkson4_joint, Fintype.sum_bool]
  simp
  norm_num

/-- **Negative check**: dropping the co-parent `1` from `MB(0)` breaks conditional
independence of `X₀` from the remaining nodes `{1, 3}`. -/
theorem berkson4_not_condIndep_drop_coparent :
    ¬ CondIndep berkson4.joint {0} ↑(univ \ insert 0 ((berkson4.markovBlanket 0).erase 1))
      ↑((berkson4.markovBlanket 0).erase 1) := by
  have e1 : (berkson4.markovBlanket 0).erase 1 = {2} := by
    rw [berkson4_markovBlanket_zero]; decide
  have e2 : univ \ insert 0 ({2} : Finset (Fin 4)) = {1, 3} := by decide
  rw [e1, e2]
  intro h
  have hx := h ![true, true, true, true]
  simp only [marginal, sum_filter, sum_four, berkson4_joint, Fintype.sum_bool] at hx
  simp at hx
  norm_num at hx

/-- **Negative check**, single node: `¬ X₀ ⫫ X₃ | X₂`; node `3` lies outside both the
reduced blanket `{2}` and the co-parent. -/
theorem berkson4_not_condIndep_zero_three :
    ¬ CondIndep berkson4.joint {0} {3} {2} := by
  intro h
  have hx := h ![true, true, true, true]
  simp only [marginal, sum_filter, sum_four, berkson4_joint, Fintype.sum_bool] at hx
  simp at hx
  norm_num at hx

/-- The non-descendants of node `3` other than its parent `1` are `0` and `2`. -/
theorem berkson4_nonDesc_three :
    {j | ¬ berkson4.IsDescendant 3 j ∧ ¬ berkson4.Edge j 3} = ({0, 2} : Set (Fin 4)) := by
  ext j
  have hd : berkson4.IsDescendant 3 j ↔ j = 3 := by
    constructor
    · intro h
      have := h.le berkson4
      fin_cases j <;> simp_all
    · rintro rfl; exact Relation.ReflTransGen.refl
  simp only [Set.mem_ofPred_eq, hd, berkson4_edge, Set.mem_insert_iff, Set.mem_singleton_iff]
  fin_cases j <;> decide

/-- **Local Markov property** at node `3`: `X₃ ⫫ X₀, X₂ | X₁`. -/
theorem berkson4_localMarkov_three :
    CondIndep berkson4.joint {3} {0, 2} {1} := by
  have h := berkson4.condIndep_localMarkov 3
  have hpa : {j | berkson4.Edge j 3} = ({1} : Set (Fin 4)) := by
    ext j
    simp only [Set.mem_ofPred_eq, berkson4_edge, Set.mem_singleton_iff]
    fin_cases j <;> decide
  rwa [berkson4_nonDesc_three, hpa] at h

end Cslib.MachineLearning.MarkovBlanketTests
