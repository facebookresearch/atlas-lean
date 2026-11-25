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

/-- Parent sets of the network: root `0`, tree nodes `1, 2` (parent `0`), reticulation `3`
(parents `1, 2`) above the hybrid species `6` (parent `3`), species `4` (parent `1`) and `5`
(parent `2`). -/
def par : Fin 7 → Finset (Fin 7) := ![∅, {0}, {0}, {1, 2}, {1}, {2}, {3}]

/-- Inheritance proportions: `γ` from `1` and `1 - γ` from `2` at the reticulation `3`, and
`1` along every tree edge. -/
noncomputable def pr (γ : ℝ) : Fin 7 → Fin 7 → ℝ :=
  ![![0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0],
    ![0, γ, 1 - γ, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0]]

/-- Node ages: root `3`, tree nodes `2` and `3/2`, reticulation `1`, species `0`. -/
noncomputable def time : Fin 7 → ℝ := ![3, 2, 3 / 2, 1, 0, 0, 0]

/-- The example network, for any `γ ∈ [0, 1]`. -/
noncomputable def network (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) : PhyloNetwork (Fin 7) where
  root := 0
  parents := par
  prop := pr γ
  parents_root := rfl
  card_parents := by decide
  prop_nonneg := by
    intro X Y
    fin_cases X <;> fin_cases Y <;> simp [pr] <;> linarith [hγ.1, hγ.2]
  prop_eq_zero := by
    intro X Y h
    fin_cases X <;> fin_cases Y <;> simp_all [par, pr]
  sum_prop := by
    intro X hX
    fin_cases X <;> simp_all [par, pr]
  wf := Subrelation.wf (r := fun Y X : Fin 7 => (Y : ℕ) < X)
    (fun {Y X} h => by fin_cases X <;> fin_cases Y <;> simp_all [par])
    (measure fun x : Fin 7 => (x : ℕ)).wf
  time := time
  time_le := by
    intro u v h
    fin_cases u <;> fin_cases v <;> simp_all [par, time] <;> norm_num

theorem parents_three (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    (network γ hγ).parents 3 = {1, 2} := rfl

theorem inherit_apply (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (v u : Fin 7) :
    (network γ hγ).inherit v u = pr γ v u := rfl

/-- Two lineages entering the reticulation: the explicit four-case mixture
`γ², γ (1 - γ), (1 - γ) γ, (1 - γ)²` has total mass `1`, as the normalization theorem says. -/
example (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    (network γ hγ).routeProb 3 ![1, 1] = γ ^ 2 ∧
      (network γ hγ).routeProb 3 ![1, 2] = γ * (1 - γ) ∧
      (network γ hγ).routeProb 3 ![2, 1] = (1 - γ) * γ ∧
      (network γ hγ).routeProb 3 ![2, 2] = (1 - γ) ^ 2 ∧
      γ ^ 2 + γ * (1 - γ) + (1 - γ) * γ + (1 - γ) ^ 2 = 1 ∧
      ∑ a : Fin 2 → Fin 7, (network γ hγ).routeProb 3 a = 1 := by
  refine ⟨?_, ?_, ?_, ?_, by ring, (network γ hγ).sum_routeProb
    (by show (3 : Fin 7) ≠ 0; decide) 2⟩ <;>
    simp [PhyloNetwork.routeProb, MathlibExt.Biology.PopulationGenetics.AdmixtureGraph.routeProb,
      network, pr, Fin.prod_univ_two] <;> ring_nf

/-- At the root a lineage has nowhere to move: the root row of the routing kernel has
total mass `0` (for one lineage, and by `routeProb_root` every assignment is `0`). -/
example (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    ∑ a : Fin 1 → Fin 7, (network γ hγ).routeProb 0 a = 0 :=
  (network γ hγ).sum_routeProb_root one_pos

/-- With `γ = 3/10` the reticulation uses both parent edges: the active graph is not a
rooted tree (the network still displays trees by selecting one reticulation edge). -/
example : ¬ Digraph.IsRootedTree (network (3 / 10) (by norm_num)).activeGraph
    (network (3 / 10) (by norm_num)).root :=
  (network (3 / 10) (by norm_num)).not_isRootedTree_activeGraph (parents_three _ _)
    (by decide) (by simp [inherit_apply, pr]; norm_num)

/-- With `γ = 1` (`γ ∈ {0, 1}`) the network displays a rooted tree. -/
example : Digraph.IsRootedTree (network 1 (by norm_num)).activeGraph
    (network 1 (by norm_num)).root := by
  refine (network 1 (by norm_num)).isRootedTree_activeGraph fun v u => ?_
  fin_cases v <;> fin_cases u <;> simp [inherit_apply, pr]

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.PhyloNetwork
