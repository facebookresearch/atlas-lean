/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.PhyloNetwork
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Tests for phylogenetic networks: one explicit network with a single reticulation (the
four-case two-lineage mixture), which is not a tree at `γ = 3 / 10` and is a rooted tree with
deterministic routing at `γ = 1`. -/

open Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.PhyloNetwork

open MathlibExt.Biology.PopulationGenetics.Coalescent


/-- Edges of the network `0 → 1, 0 → 2, 1 → 3, 2 → 3, 1 → 4, 2 → 5, 3 → 6`: root `0`, tree nodes
`1, 2`, reticulation `3` (parents `1, 2`) above the hybrid species `6`, species `4, 5`. -/
def edges : Finset (Fin 7 × Fin 7) := {(0, 1), (0, 2), (1, 3), (2, 3), (1, 4), (2, 5), (3, 6)}

/-- The network's digraph. -/
def graph : Digraph (Fin 7) where
  Adj u v := (u, v) ∈ edges

instance : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable ((u, v) ∈ edges))

theorem lt_of_adj : ∀ u v, graph.Adj u v → u < v := by decide

theorem isAcyclic_graph : graph.IsAcyclic := by
  intro v hv
  have key : ∀ a b, Relation.TransGen graph.Adj a b → a < b := fun a b hab => by
    induction hab with
    | single h => exact lt_of_adj _ _ h
    | tail _ h ih => exact ih.trans (lt_of_adj _ _ h)
  exact lt_irrefl v (key v v hv)

theorem parentsOf_graph_three : parentsOf graph 3 = {1, 2} := by decide

/-- Node ages: root `3`, tree nodes `2` and `3/2`, reticulation `1`, species `0`. -/
noncomputable def time : Fin 7 → ℝ := ![3, 2, 3 / 2, 1, 0, 0, 0]

/-- Inheritance probabilities: `γ` from `1` and `1 - γ` from `2` at the reticulation `3`, and `1`
along every tree edge. -/
noncomputable def inherit (γ : ℝ) (v u : Fin 7) : ℝ :=
  if v = 3 then (if u = 1 then γ else if u = 2 then 1 - γ else 0)
  else if (u, v) ∈ edges then 1 else 0

/-- The example network, for any `γ ∈ [0, 1]`. -/
noncomputable def network (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) : PhyloNetwork (Fin 7) where
  G := graph
  root := 0
  isAcyclic := isAcyclic_graph
  parentsOf_root := by decide
  card_parentsOf := by decide
  time := time
  time_le := by
    intro u v h
    fin_cases u <;> fin_cases v <;> revert h <;> simp [graph, edges, time] <;> norm_num
  inherit := inherit γ
  inherit_nonneg := by
    intro v u
    simp only [inherit]
    split_ifs <;> linarith [hγ.1, hγ.2]
  inherit_eq_zero := by
    intro v u hu
    simp only [inherit]
    split_ifs with h3 h1 h2 he
    · subst h3; subst h1; exact absurd (by decide) hu
    · subst h3; subst h2; exact absurd (by decide) hu
    · rfl
    · exact absurd (by simp only [parentsOf, Finset.mem_filter, Finset.mem_univ, true_and]; exact he) hu
    · rfl
  sum_inherit := by
    intro v hv
    fin_cases v
    · exact absurd rfl hv
    all_goals simp [parentsOf, graph, edges, inherit, Finset.sum_filter, Fin.sum_univ_succ]

theorem parents_three (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    (network γ hγ).parents 3 = {1, 2} := parentsOf_graph_three

/-- Two lineages entering the reticulation: the explicit four-case mixture
`γ², γ (1 - γ), (1 - γ) γ, (1 - γ)²` has total mass `1`, as the normalization theorem says. -/
example (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    (network γ hγ).routeProb 3 ![1, 1] = γ ^ 2 ∧
      (network γ hγ).routeProb 3 ![1, 2] = γ * (1 - γ) ∧
      (network γ hγ).routeProb 3 ![2, 1] = (1 - γ) * γ ∧
      (network γ hγ).routeProb 3 ![2, 2] = (1 - γ) ^ 2 ∧
      γ ^ 2 + γ * (1 - γ) + (1 - γ) * γ + (1 - γ) ^ 2 = 1 ∧
      ∑ a : Fin 2 → Fin 7, (network γ hγ).routeProb 3 a = 1 := by
  refine ⟨?_, ?_, ?_, ?_, by ring, (network γ hγ).sum_routeProb (by show (3 : Fin 7) ≠ 0; decide) 2⟩ <;>
    simp [PhyloNetwork.routeProb, network, inherit, Fin.prod_univ_two] <;> ring_nf

/-- With `γ = 3/10` the reticulation uses both parent edges: the active graph is not a
rooted tree (the network still displays trees by selecting one reticulation edge). -/
example : ¬ PhyloNetwork.IsRootedTree (network (3 / 10) (by norm_num)).activeGraph
    (network (3 / 10) (by norm_num)).root :=
  (network (3 / 10) (by norm_num)).not_isRootedTree_activeGraph (parents_three _ _)
    (by decide) (by simp [network, inherit]; norm_num)

/-- With `γ = 1` (`γ ∈ {0, 1}`) the network displays a rooted tree. -/
example : PhyloNetwork.IsRootedTree (network 1 (by norm_num)).activeGraph
    (network 1 (by norm_num)).root := by
  refine (network 1 (by norm_num)).isRootedTree_activeGraph fun v u => ?_
  simp only [network, inherit]
  split_ifs <;> norm_num

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.PhyloNetwork
