/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ShapleyValueFormula
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

open MathlibExt.GameTheory.ShapleyValue

/-- With two players, each coalition size has weight `1/2`. -/
example : shapleyWeight 2 1 = 1 / 2 ∧ shapleyWeight 2 2 = 1 / 2 := by
  constructor <;> norm_num [shapleyWeight, Nat.factorial]

/-- With three players the weights of sizes `1, 2, 3` are `1/3, 1/6, 1/3`. -/
example : shapleyWeight 3 1 = 1 / 3 ∧ shapleyWeight 3 2 = 1 / 6 ∧ shapleyWeight 3 3 = 1 / 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [shapleyWeight, Nat.factorial]

open Classical in
/-- A two-player game: player `0` alone earns `1`, player `1` alone earns `0`, together they earn
`3`. -/
noncomputable def twoPlayerGame : CoopGame (Fin 2) where
  charFun S := if S = Set.univ then 3 else if (0 : Fin 2) ∈ S then 1 else 0
  empty := by simp [Set.empty_ne_univ]

/-- Any value satisfying Shapley's axioms pays player `0` its average marginal contribution
`½ · (1 − 0) + ½ · (3 − 0) = 2`. -/
example (φ : CoopGame (Fin 2) →ₗ[ℝ] (Fin 2 → ℝ)) (he : IsEfficient φ) (hs : IsSymmetric φ)
    (hn : SatisfiesNullPlayerAxiom φ) : φ twoPlayerGame 0 = 2 := by
  rw [eq_shapleyFormula he hs hn, shapleyFormula_apply]
  have hfilter : Finset.univ.filter (fun S : Finset (Fin 2) => (0 : Fin 2) ∈ S) =
      {{0}, Finset.univ} := by decide
  rw [hfilter, Finset.sum_pair (by decide)]
  have hw1 : shapleyWeight 2 1 = 1 / 2 := by norm_num [shapleyWeight, Nat.factorial]
  have hw2 : shapleyWeight 2 2 = 1 / 2 := by norm_num [shapleyWeight, Nat.factorial]
  simp [twoPlayerGame, hw1, hw2, Set.empty_ne_univ]
  norm_num
