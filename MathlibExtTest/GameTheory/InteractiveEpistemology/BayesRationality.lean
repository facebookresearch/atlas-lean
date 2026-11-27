/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.InteractiveEpistemology.BayesRationality

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

open MathlibExt.GameTheory.InteractiveEpistemology
open MathlibExt.GameTheory.CorrelatedEquilibrium

/-! A public fair coin `ω : Fin 2` tells both players of a coordination game which action to
play. Both are Bayes rational at every state, so by Aumann's Main Theorem the distribution
`½ (0,0) + ½ (1,1)` is a correlated equilibrium; it is not a product distribution. -/

/-- The coordination game in cost form: cost `0` if the actions match, `1` otherwise. -/
def coordCost (_ : Fin 2) (t : Fin 2 → Fin 2) : ℝ := if t 0 = t 1 then 0 else 1

/-- Both players play the coin's value. -/
def coinPlay (ω : Fin 2) : Fin 2 → Fin 2 := fun _ => ω

theorem coin_nonneg : ∀ _ω : Fin 2, (0 : ℝ) ≤ 1 / 2 := fun _ => by norm_num

theorem coin_sum : ∑ _ω : Fin 2, (1 / 2 : ℝ) = 1 := by norm_num

theorem coinPlay_bayesRational (i : Fin 2) (ω : Fin 2) :
    IsBayesRational (fun _ => (1 / 2 : ℝ)) coin_nonneg coin_sum (fun _ => ⊥) coordCost coinPlay i
      ω := by
  rw [isBayesRational_iff_sum coin_nonneg coin_sum]
  intro k
  refine Finset.sum_nonpos fun x _ => ?_
  have h0 : coordCost i (coinPlay x) = 0 := by simp [coordCost, coinPlay]
  have h1 : 0 ≤ coordCost i (Function.update (coinPlay x) i k) := by
    unfold coordCost; split_ifs <;> norm_num
  rw [h0]
  nlinarith

/-- Aumann's Main Theorem applied to the public coin. -/
example : IsCorrelatedEq coordCost
    (fun t => ∑ _ω ∈ Finset.univ.filter (fun ω => coinPlay ω = t), (1 / 2 : ℝ)) 0 :=
  isCorrelatedEq_of_isBayesRational coin_nonneg coin_sum (fun _ => ⊥)
    coordCost coinPlay (fun _ => bot_le) coinPlay_bayesRational

/-- The resulting distribution puts mass `½` on `(0, 0)` and `0` on `(0, 1)`, so it is not a
product of its marginals (each marginal is uniform). -/
example : (∑ _ω ∈ Finset.univ.filter (fun ω => coinPlay ω = ![0, 0]), (1 / 2 : ℝ)) = 1 / 2 ∧
    (∑ _ω ∈ Finset.univ.filter (fun ω => coinPlay ω = ![0, 1]), (1 / 2 : ℝ)) = 0 := by
  constructor
  · have : Finset.univ.filter (fun ω : Fin 2 => coinPlay ω = ![0, 0]) = {0} := by
      ext ω; fin_cases ω <;> simp [coinPlay, funext_iff, Fin.forall_fin_two]
    simp [this]
  · have : Finset.univ.filter (fun ω : Fin 2 => coinPlay ω = ![0, 1]) = ∅ := by
      ext ω; fin_cases ω <;> simp [coinPlay, funext_iff, Fin.forall_fin_two]
    simp [this]

/-- The converse applied to Aumann's correlated equilibrium of Chicken: it is the distribution of
Bayes-rational play in an information system (the profiles themselves, each player told only
its own recommendation). -/
example (i : Fin 2) (t : Fin 2 → Fin 2) :
    IsBayesRational chickenCE chickenCE_isCorrelatedEq.1.1 chickenCE_isCorrelatedEq.1.2
      (fun i => Setoid.ker fun t : Fin 2 → Fin 2 => t i) chickenCost id i t :=
  isBayesRational_of_isCorrelatedEq chickenCE_isCorrelatedEq i t

/-! The common prior must be a probability distribution: for the zero prior, under which every
action would be Bayes rational, the proof of `∑ p = 1` cannot be given. -/

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : Prop :=
  IsBayesRational (fun _ : Fin 2 => (0 : ℝ)) (fun _ => le_rfl) (by simp) (fun _ => ⊥) coordCost
    coinPlay 0 0
