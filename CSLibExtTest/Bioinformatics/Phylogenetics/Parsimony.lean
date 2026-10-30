/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.Parsimony

/-!
# Tests for Sankoff's and Fitch's parsimony algorithms

On the three-leaf tree `((a, b), c)` over binary states with observed states `a = 1`, `b = 0`,
`c = 0` and unit costs: Sankoff's costs at the root (`1` for state `0`, `2` for state `1`),
Fitch's set `{0}` and count `1`, their agreement (`fitch_score_eq`, `fitch_set_eq`), an optimal
labeling and its cost, a labeling that disagrees with a leaf (excluded from the minimum), the
leaf boundary cases (`⊤` at a state other than the observed one), and a weighted cost matrix in
which one change is forbidden.
-/

@[expose] public section

namespace CSLibExtTest.Bioinformatics.Phylogenetics.Parsimony

open Cslib.Bioinformatics.Phylogenetics FelsensteinPruning Tree Parsimony MinTropical

/-- Observed states at the three leaves. -/
def σ₀ : Fin 3 → Bool
  | 0 => true
  | _ => false

/-- The tree `((0, 1), 2)` with unit costs on every edge. -/
def t₀ : Tree (Fin 3) Bool Cost :=
  node unitCost (node unitCost (leaf 0) unitCost (leaf 1)) unitCost (leaf 2)

theorem t₀_isUnitCost : IsUnitCost t₀ := by simp [t₀, IsUnitCost]

-- Leaves: cost `0` at the observed state and `⊤` elsewhere.
example : sankoff σ₀ (leaf 0) true = 0 := by simp [sankoff_leaf, σ₀]
example : sankoff σ₀ (leaf 0) false = ⊤ := by simp [sankoff_leaf, σ₀]

-- Sankoff's costs at the root.
theorem sankoff_t₀_false : sankoff σ₀ t₀ false = 1 := by
  simp [t₀, sankoff_node, sankoff_leaf, σ₀, unitCost, Fintype.univ_bool]

theorem sankoff_t₀_true : sankoff σ₀ t₀ true = 2 := by
  simp [t₀, sankoff_node, sankoff_leaf, σ₀, unitCost, Fintype.univ_bool]
  decide

-- Fitch's algorithm: set `{0}` (state `false`) and one change.
example : fitch σ₀ t₀ = ({false}, 1) := by decide

-- Fitch agrees with Sankoff.
example : ((fitch σ₀ t₀).2 : WithTop ℕ) = Finset.univ.inf (sankoff σ₀ t₀) :=
  fitch_score_eq σ₀ t₀ t₀_isUnitCost

example : Finset.univ.inf (sankoff σ₀ t₀) = 1 := by
  rw [← fitch_score_eq σ₀ t₀ t₀_isUnitCost]; decide

example : (fitch σ₀ t₀).1 = Finset.univ.filter (fun s => sankoff σ₀ t₀ s = (fitch σ₀ t₀).2) :=
  fitch_set_eq σ₀ t₀ t₀_isUnitCost

/-- The labeling with root `0`, inner vertex `0`, and leaves `1, 0, 0`. -/
def x₀ : Labeling t₀ := ((false, ((true, ⟨⟩), (false, ⟨⟩))), (false, ⟨⟩))

-- It agrees with the leaves and attains the minimum `1`.
example : Agrees σ₀ t₀ false x₀ := by decide
example : edgeCost t₀ false x₀ = 1 := by
  simp [x₀, t₀, edgeCost, unitCost]
example : sankoff σ₀ t₀ false ≤ edgeCost t₀ false x₀ :=
  sankoff_le_edgeCost σ₀ t₀ false x₀ (by decide)

-- A labeling that puts state `0` at leaf `0` disagrees with the observation.
/-- The labeling with state `0` everywhere. -/
def x₁ : Labeling t₀ := ((false, ((false, ⟨⟩), (false, ⟨⟩))), (false, ⟨⟩))

example : ¬ Agrees σ₀ t₀ false x₁ := by decide

-- An optimal labeling exists.
example : ∃ x, Agrees σ₀ t₀ false x ∧ edgeCost t₀ false x = sankoff σ₀ t₀ false :=
  exists_edgeCost_eq_sankoff σ₀ t₀ false (by rw [sankoff_t₀_false]; decide)

/-- A cost matrix in which the change `0 → 1` is forbidden and `1 → 0` costs `3`. -/
def c₁ : Bool → Bool → Cost
  | false, true => trop ⊤
  | true, false => trop 3
  | _, _ => trop 0

/-- The cherry `(0, 1)` with cost `c₁` on both edges. -/
def t₁ : Tree (Fin 3) Bool Cost := node c₁ (leaf 0) c₁ (leaf 1)

-- Root `0` is impossible (leaf `0` has state `1`); root `1` costs `3`.
example : sankoff σ₀ t₁ false = ⊤ := by
  simp [t₁, sankoff_node, sankoff_leaf, σ₀, c₁, Fintype.univ_bool]
example : sankoff σ₀ t₁ true = 3 := by
  simp [t₁, sankoff_node, sankoff_leaf, σ₀, c₁, Fintype.univ_bool]

end CSLibExtTest.Bioinformatics.Phylogenetics.Parsimony
