/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.BayesianGame
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false

@[expose] public section

open scoped BigOperators

namespace MathlibExtTest.GameTheory.BayesianGame

open MathlibExt.GameTheory
open MathlibExt.GameTheory.BayesianGame

/-- Uniform prior over the four type profiles of the example game. -/
noncomputable def exPrior : (Fin 2 → Fin 2) → ℝ := fun _ => 1 / 4

/-- Payoffs of the example game: player 1 is paid for matching their type,
player 0 is paid for matching player 1's action, more so at type 0. -/
def exUtility (i : Fin 2) (θ a : Fin 2 → Fin 2) : ℝ :=
  if i = 0 then (if a 0 = a 1 then (if θ 1 = 0 then 2 else 1) else 0)
  else (if a 1 = θ 1 then 1 else 0)

/-- The candidate equilibrium: player 0 always plays 0, player 1 plays their type. -/
def sStar : ∀ (_ : Fin 2) (_ : Fin 2), Fin 2 := fun i θi => if i = 0 then 0 else θi

/-- The two actions are distinct. -/
theorem h10 : (1 : Fin 2) ≠ 0 := by decide

/-- The two actions are distinct, symmetrically. -/
theorem h01 : (0 : Fin 2) ≠ 1 := by decide

/-- Every element of `Fin 2` is 0 or 1. -/
theorem h2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide

/-- Player 0's payoff, with the player index resolved. -/
theorem exUtility_zero (θ a : Fin 2 → Fin 2) :
    exUtility 0 θ a = (if a 0 = a 1 then (if θ 1 = 0 then 2 else 1) else 0) := by
  simp [exUtility]

/-- Player 1's payoff, with the player index resolved. -/
theorem exUtility_one (θ a : Fin 2 → Fin 2) :
    exUtility 1 θ a = (if a 1 = θ 1 then 1 else 0) := by
  simp [exUtility]

/-- The candidate profile prescribes 0 for player 0. -/
theorem sStar_zero (x : Fin 2) : sStar 0 x = 0 := by simp [sStar]

/-- The candidate profile prescribes the type for player 1. -/
theorem sStar_one (x : Fin 2) : sStar 1 x = x := by simp [sStar]

/-- There are four type profiles. -/
theorem card_profiles : Fintype.card (Fin 2 → Fin 2) = 4 := by
  rw [Fintype.card_pi]
  norm_num [Fintype.card_fin, Fin.prod_univ_two]

/-- Conditioning on one player's type leaves two profiles. -/
theorem filter_card (i : Fin 2) (θi : Fin 2) :
    (Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ i = θi)).card = 2 := by
  fin_cases i <;> fin_cases θi <;> decide

/-- The profiles with player 0 of type 0. -/
theorem filter_00 :
    Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 0 = 0) = {![0, 0], ![0, 1]} := by
  decide

/-- The profiles with player 0 of type 1. -/
theorem filter_01 :
    Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 0 = 1) = {![1, 0], ![1, 1]} := by
  decide

/-- The profiles with player 1 of type 0. -/
theorem filter_10 :
    Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 1 = 0) = {![0, 0], ![1, 0]} := by
  decide

/-- The profiles with player 1 of type 1. -/
theorem filter_11 :
    Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 1 = 1) = {![0, 1], ![1, 1]} := by
  decide

/-- Profiles `![0, 0]` and `![0, 1]` differ. -/
theorem hne0001 : (![0, 0] : Fin 2 → Fin 2) ≠ ![0, 1] := by decide
/-- Profiles `![1, 0]` and `![1, 1]` differ. -/
theorem hne1011 : (![1, 0] : Fin 2 → Fin 2) ≠ ![1, 1] := by decide
/-- Profiles `![0, 0]` and `![1, 0]` differ. -/
theorem hne0010 : (![0, 0] : Fin 2 → Fin 2) ≠ ![1, 0] := by decide
/-- Profiles `![0, 1]` and `![1, 1]` differ. -/
theorem hne0111 : (![0, 1] : Fin 2 → Fin 2) ≠ ![1, 1] := by decide

/-- The example Bayesian game. -/
noncomputable def exGame : BayesianGame (Fin 2) (fun _ => Fin 2) (fun _ => Fin 2) where
  prior := exPrior
  prior_nonneg := fun θ => by simp only [exPrior]; norm_num
  prior_sum := by
    show ∑ θ : Fin 2 → Fin 2, exPrior θ = 1
    simp only [exPrior, Finset.sum_const, Finset.card_univ, card_profiles]
    norm_num
  prior_pos := fun i θi => by
    show (0 : ℝ) < ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ i = θi),
      exPrior θ
    simp only [exPrior, Finset.sum_const, filter_card i θi]
    norm_num
  utility := exUtility
  action_nonempty := fun _ => ⟨0⟩

/-- Marginal of player 0's type 0. -/
theorem marg00 : exGame.marginal 0 0 = 1 / 2 := by
  show (∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 0 = 0), exPrior θ) = 1 / 2
  rw [filter_00, Finset.sum_pair hne0001]
  norm_num [exPrior]

/-- Marginal of player 0's type 1. -/
theorem marg01 : exGame.marginal 0 1 = 1 / 2 := by
  show (∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 0 = 1), exPrior θ) = 1 / 2
  rw [filter_01, Finset.sum_pair hne1011]
  norm_num [exPrior]

/-- Marginal of player 1's type 0. -/
theorem marg10 : exGame.marginal 1 0 = 1 / 2 := by
  show (∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 1 = 0), exPrior θ) = 1 / 2
  rw [filter_10, Finset.sum_pair hne0010]
  norm_num [exPrior]

/-- Marginal of player 1's type 1. -/
theorem marg11 : exGame.marginal 1 1 = 1 / 2 := by
  show (∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 1 = 1), exPrior θ) = 1 / 2
  rw [filter_11, Finset.sum_pair hne0111]
  norm_num [exPrior]

/-- Base interim value at player 0, type 0. -/
theorem t1base00 : MechanismDesign.interimUtility exGame.prior exGame.utility 0 0
    (fun θ => id (fun j => sStar j (θ j))) = 1 / 2 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 0 = 0),
      exPrior θ * exUtility 0 θ (fun j => sStar j (θ j)) = 1 / 2
  rw [filter_00, Finset.sum_pair hne0001]
  norm_num [exPrior, exUtility_zero, exUtility_one, sStar_zero, sStar_one,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Base interim value at player 0, type 1. -/
theorem t1base01 : MechanismDesign.interimUtility exGame.prior exGame.utility 0 1
    (fun θ => id (fun j => sStar j (θ j))) = 1 / 2 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 0 = 1),
      exPrior θ * exUtility 0 θ (fun j => sStar j (θ j)) = 1 / 2
  rw [filter_01, Finset.sum_pair hne1011]
  norm_num [exPrior, exUtility_zero, exUtility_one, sStar_zero, sStar_one,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Base interim value at player 1, type 0. -/
theorem t1base10 : MechanismDesign.interimUtility exGame.prior exGame.utility 1 0
    (fun θ => id (fun j => sStar j (θ j))) = 1 / 2 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 1 = 0),
      exPrior θ * exUtility 1 θ (fun j => sStar j (θ j)) = 1 / 2
  rw [filter_10, Finset.sum_pair hne0010]
  norm_num [exPrior, exUtility_zero, exUtility_one, sStar_zero, sStar_one,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Base interim value at player 1, type 1. -/
theorem t1base11 : MechanismDesign.interimUtility exGame.prior exGame.utility 1 1
    (fun θ => id (fun j => sStar j (θ j))) = 1 / 2 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 1 = 1),
      exPrior θ * exUtility 1 θ (fun j => sStar j (θ j)) = 1 / 2
  rw [filter_11, Finset.sum_pair hne0111]
  norm_num [exPrior, exUtility_zero, exUtility_one, sStar_zero, sStar_one,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Deviating to 0 at player 0, type 0. -/
theorem t1dev000 : MechanismDesign.interimUtility exGame.prior exGame.utility 0 0
    (fun θ => id (Function.update (fun j => sStar j (θ j)) 0 0)) = 1 / 2 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 0 = 0),
      exPrior θ * exUtility 0 θ (Function.update (fun j => sStar j (θ j)) 0 0) = 1 / 2
  rw [filter_00, Finset.sum_pair hne0001]
  norm_num [exPrior, exUtility_zero, exUtility_one, sStar_zero, sStar_one,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Deviating to 1 at player 0, type 0. -/
theorem t1dev001 : MechanismDesign.interimUtility exGame.prior exGame.utility 0 0
    (fun θ => id (Function.update (fun j => sStar j (θ j)) 0 1)) = 1 / 4 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 0 = 0),
      exPrior θ * exUtility 0 θ (Function.update (fun j => sStar j (θ j)) 0 1) = 1 / 4
  rw [filter_00, Finset.sum_pair hne0001]
  norm_num [exPrior, exUtility_zero, exUtility_one, sStar_zero, sStar_one,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Deviating to 0 at player 0, type 1. -/
theorem t1dev010 : MechanismDesign.interimUtility exGame.prior exGame.utility 0 1
    (fun θ => id (Function.update (fun j => sStar j (θ j)) 0 0)) = 1 / 2 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 0 = 1),
      exPrior θ * exUtility 0 θ (Function.update (fun j => sStar j (θ j)) 0 0) = 1 / 2
  rw [filter_01, Finset.sum_pair hne1011]
  norm_num [exPrior, exUtility_zero, exUtility_one, sStar_zero, sStar_one,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Deviating to 1 at player 0, type 1. -/
theorem t1dev011 : MechanismDesign.interimUtility exGame.prior exGame.utility 0 1
    (fun θ => id (Function.update (fun j => sStar j (θ j)) 0 1)) = 1 / 4 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 0 = 1),
      exPrior θ * exUtility 0 θ (Function.update (fun j => sStar j (θ j)) 0 1) = 1 / 4
  rw [filter_01, Finset.sum_pair hne1011]
  norm_num [exPrior, exUtility_zero, exUtility_one, sStar_zero, sStar_one,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Deviating to 0 at player 1, type 0. -/
theorem t1dev100 : MechanismDesign.interimUtility exGame.prior exGame.utility 1 0
    (fun θ => id (Function.update (fun j => sStar j (θ j)) 1 0)) = 1 / 2 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 1 = 0),
      exPrior θ * exUtility 1 θ (Function.update (fun j => sStar j (θ j)) 1 0) = 1 / 2
  rw [filter_10, Finset.sum_pair hne0010]
  norm_num [exPrior, exUtility_zero, exUtility_one, sStar_zero, sStar_one,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Deviating to 1 at player 1, type 0. -/
theorem t1dev101 : MechanismDesign.interimUtility exGame.prior exGame.utility 1 0
    (fun θ => id (Function.update (fun j => sStar j (θ j)) 1 1)) = 0 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 1 = 0),
      exPrior θ * exUtility 1 θ (Function.update (fun j => sStar j (θ j)) 1 1) = 0
  rw [filter_10, Finset.sum_pair hne0010]
  norm_num [exPrior, exUtility_zero, exUtility_one, sStar_zero, sStar_one,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Deviating to 0 at player 1, type 1. -/
theorem t1dev110 : MechanismDesign.interimUtility exGame.prior exGame.utility 1 1
    (fun θ => id (Function.update (fun j => sStar j (θ j)) 1 0)) = 0 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 1 = 1),
      exPrior θ * exUtility 1 θ (Function.update (fun j => sStar j (θ j)) 1 0) = 0
  rw [filter_11, Finset.sum_pair hne0111]
  norm_num [exPrior, exUtility_zero, exUtility_one, sStar_zero, sStar_one,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Deviating to 1 at player 1, type 1. -/
theorem t1dev111 : MechanismDesign.interimUtility exGame.prior exGame.utility 1 1
    (fun θ => id (Function.update (fun j => sStar j (θ j)) 1 1)) = 1 / 2 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 1 = 1),
      exPrior θ * exUtility 1 θ (Function.update (fun j => sStar j (θ j)) 1 1) = 1 / 2
  rw [filter_11, Finset.sum_pair hne0111]
  norm_num [exPrior, exUtility_zero, exUtility_one, sStar_zero, sStar_one,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- The candidate profile is a Bayesian Nash equilibrium. -/
theorem t1_example_isBayesNash : exGame.IsBayesNash sStar := by
  show ∀ (i : Fin 2) (θi : Fin 2) (a : Fin 2),
    MechanismDesign.interimUtility exGame.prior exGame.utility i θi
      (fun θ => id (Function.update (fun j => sStar j (θ j)) i a)) ≤
    MechanismDesign.interimUtility exGame.prior exGame.utility i θi
      (fun θ => id (fun j => sStar j (θ j)))
  rw [Fin.forall_fin_two]
  constructor
  · rw [Fin.forall_fin_two]
    constructor
    · rw [Fin.forall_fin_two]
      constructor
      · rw [t1dev000, t1base00]
      · rw [t1dev001, t1base00]; norm_num
    · rw [Fin.forall_fin_two]
      constructor
      · rw [t1dev010, t1base01]
      · rw [t1dev011, t1base01]; norm_num
  · rw [Fin.forall_fin_two]
    constructor
    · rw [Fin.forall_fin_two]
      constructor
      · rw [t1dev100, t1base10]
      · rw [t1dev101, t1base10]; norm_num
    · rw [Fin.forall_fin_two]
      constructor
      · rw [t1dev110, t1base11]; norm_num
      · rw [t1dev111, t1base11]

/-- Base interim value at player 1, type 0, when the plan plays 1 there. -/
theorem t2base10neg (s : ∀ _ : Fin 2, Fin 2 → Fin 2) (h : s 1 0 = 1) :
    MechanismDesign.interimUtility exGame.prior exGame.utility 1 0
      (fun θ => id (fun j => s j (θ j))) = 0 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 1 = 0),
      exPrior θ * exUtility 1 θ (fun j => s j (θ j)) = 0
  rw [filter_10, Finset.sum_pair hne0010]
  norm_num [exPrior, exUtility_zero, exUtility_one, h,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Base interim value at player 1, type 1, when the plan plays 0 there. -/
theorem t2base11neg (s : ∀ _ : Fin 2, Fin 2 → Fin 2) (h : s 1 1 = 0) :
    MechanismDesign.interimUtility exGame.prior exGame.utility 1 1
      (fun θ => id (fun j => s j (θ j))) = 0 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 1 = 1),
      exPrior θ * exUtility 1 θ (fun j => s j (θ j)) = 0
  rw [filter_11, Finset.sum_pair hne0111]
  norm_num [exPrior, exUtility_zero, exUtility_one, h,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Deviating to 0 at player 1, type 0, for any plan. -/
theorem t2dev100 (s : ∀ _ : Fin 2, Fin 2 → Fin 2) :
    MechanismDesign.interimUtility exGame.prior exGame.utility 1 0
      (fun θ => id (Function.update (fun j => s j (θ j)) 1 0)) = 1 / 2 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 1 = 0),
      exPrior θ * exUtility 1 θ (Function.update (fun j => s j (θ j)) 1 0) = 1 / 2
  rw [filter_10, Finset.sum_pair hne0010]
  norm_num [exPrior, exUtility_zero, exUtility_one,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Deviating to 1 at player 1, type 1, for any plan. -/
theorem t2dev111 (s : ∀ _ : Fin 2, Fin 2 → Fin 2) :
    MechanismDesign.interimUtility exGame.prior exGame.utility 1 1
      (fun θ => id (Function.update (fun j => s j (θ j)) 1 1)) = 1 / 2 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 1 = 1),
      exPrior θ * exUtility 1 θ (Function.update (fun j => s j (θ j)) 1 1) = 1 / 2
  rw [filter_11, Finset.sum_pair hne0111]
  norm_num [exPrior, exUtility_zero, exUtility_one,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Base interim value at player 0, type 0, when the plan plays 1 there. -/
theorem t2base00neg_of (s : ∀ _ : Fin 2, Fin 2 → Fin 2) (e10 : s 1 0 = 0)
    (e11 : s 1 1 = 1) (h : s 0 0 = 1) :
    MechanismDesign.interimUtility exGame.prior exGame.utility 0 0
      (fun θ => id (fun j => s j (θ j))) = 1 / 4 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 0 = 0),
      exPrior θ * exUtility 0 θ (fun j => s j (θ j)) = 1 / 4
  rw [filter_00, Finset.sum_pair hne0001]
  norm_num [exPrior, exUtility_zero, exUtility_one, e10, e11, h,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Base interim value at player 0, type 1, when the plan plays 1 there. -/
theorem t2base01neg_of (s : ∀ _ : Fin 2, Fin 2 → Fin 2) (e10 : s 1 0 = 0)
    (e11 : s 1 1 = 1) (h : s 0 1 = 1) :
    MechanismDesign.interimUtility exGame.prior exGame.utility 0 1
      (fun θ => id (fun j => s j (θ j))) = 1 / 4 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 0 = 1),
      exPrior θ * exUtility 0 θ (fun j => s j (θ j)) = 1 / 4
  rw [filter_01, Finset.sum_pair hne1011]
  norm_num [exPrior, exUtility_zero, exUtility_one, e10, e11, h,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Deviating to 0 at player 0, type 0, given player 1 plays their type. -/
theorem t2dev000_of (s : ∀ _ : Fin 2, Fin 2 → Fin 2) (e10 : s 1 0 = 0)
    (e11 : s 1 1 = 1) :
    MechanismDesign.interimUtility exGame.prior exGame.utility 0 0
      (fun θ => id (Function.update (fun j => s j (θ j)) 0 0)) = 1 / 2 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 0 = 0),
      exPrior θ * exUtility 0 θ (Function.update (fun j => s j (θ j)) 0 0) = 1 / 2
  rw [filter_00, Finset.sum_pair hne0001]
  norm_num [exPrior, exUtility_zero, exUtility_one, e10, e11,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- Deviating to 0 at player 0, type 1, given player 1 plays their type. -/
theorem t2dev010_of (s : ∀ _ : Fin 2, Fin 2 → Fin 2) (e10 : s 1 0 = 0)
    (e11 : s 1 1 = 1) :
    MechanismDesign.interimUtility exGame.prior exGame.utility 0 1
      (fun θ => id (Function.update (fun j => s j (θ j)) 0 0)) = 1 / 2 := by
  show ∑ θ ∈ Finset.univ.filter (fun θ : Fin 2 → Fin 2 => θ 0 = 1),
      exPrior θ * exUtility 0 θ (Function.update (fun j => s j (θ j)) 0 0) = 1 / 2
  rw [filter_01, Finset.sum_pair hne1011]
  norm_num [exPrior, exUtility_zero, exUtility_one, e10, e11,
    Function.update_self, Function.update_of_ne, h10, h01]

/-- The candidate profile is the unique Bayesian Nash equilibrium. -/
theorem t2_example_unique : ∀ s, exGame.IsBayesNash s → s = sStar := by
  intro s hs
  have e10 : s 1 0 = 0 := by
    rcases h2 (s 1 0) with h | h
    · exact h
    · have hcon := hs 1 0 0
      rw [t2dev100 s, t2base10neg s h] at hcon
      norm_num at hcon
  have e11 : s 1 1 = 1 := by
    rcases h2 (s 1 1) with h | h
    · have hcon := hs 1 1 1
      rw [t2dev111 s, t2base11neg s h] at hcon
      norm_num at hcon
    · exact h
  have e00 : s 0 0 = 0 := by
    rcases h2 (s 0 0) with h | h
    · exact h
    · have hcon := hs 0 0 0
      rw [t2dev000_of s e10 e11, t2base00neg_of s e10 e11 h] at hcon
      norm_num at hcon
  have e01 : s 0 1 = 0 := by
    rcases h2 (s 0 1) with h | h
    · exact h
    · have hcon := hs 0 1 0
      rw [t2dev010_of s e10 e11, t2base01neg_of s e10 e11 h] at hcon
      norm_num at hcon
  have all : ∀ (i θi : Fin 2), s i θi = sStar i θi := by
    rw [Fin.forall_fin_two]
    constructor
    · rw [Fin.forall_fin_two]
      constructor
      · simp [e00, sStar_zero]
      · simp [e01, sStar_zero]
    · rw [Fin.forall_fin_two]
      constructor
      · simp [e10, sStar_one]
      · simp [e11, sStar_one]
  funext i θi
  exact all i θi

/-- The deviating plan profile, as an outcome rule. -/
theorem dev_h_eq (i : Fin 2) (a : Fin 2) :
    (fun θ : Fin 2 → Fin 2 => fun j => (Function.update sStar i (fun _ => a)) j (θ j)) =
      (fun θ => id (Function.update (fun j => sStar j (θ j)) i a)) := by
  funext θ
  exact (update_action_eq sStar i a θ).symm

/-- The base plan profile, as an outcome rule. -/
theorem base_h_eq :
    (fun θ : Fin 2 → Fin 2 => fun j => sStar j (θ j)) =
      (fun θ => id (fun j => sStar j (θ j))) :=
  rfl

/-- An agent deviation pays the deviating plan's ex-interim utility. -/
theorem agent_payoff_eq (i θi : Fin 2) (t : Fin 2) :
    exGame.condInterim
      (agentProfileEquiv.symm (Function.update (agentProfileEquiv sStar) ⟨i, θi⟩ t)) i θi =
    exGame.condInterim (Function.update sStar i (fun _ => t)) i θi := by
  apply condInterim_congr
  intro θ hθ
  exact agent_dev_agree sStar i θi t θ (Finset.mem_filter.mp hθ).2

/-- The undeviated agent payoff is the candidate's ex-interim utility. -/
theorem agent_base_eq (i θi : Fin 2) :
    exGame.condInterim
      (agentProfileEquiv.symm (Function.update (agentProfileEquiv sStar) ⟨i, θi⟩
        ((agentProfileEquiv sStar) ⟨i, θi⟩))) i θi =
    exGame.condInterim sStar i θi := by
  rw [Function.update_eq_self, agentProfileEquiv.symm_apply_apply]

/-- Every agent best-responds in the agent form at the candidate profile. -/
theorem t3_all : ∀ (i θi t : Fin 2),
    exGame.condInterim
      (agentProfileEquiv.symm (Function.update (agentProfileEquiv sStar) ⟨i, θi⟩ t)) i θi ≤
    exGame.condInterim
      (agentProfileEquiv.symm (Function.update (agentProfileEquiv sStar) ⟨i, θi⟩
        ((agentProfileEquiv sStar) ⟨i, θi⟩))) i θi := by
  rw [Fin.forall_fin_two]
  constructor
  · rw [Fin.forall_fin_two]
    constructor
    · rw [Fin.forall_fin_two]
      constructor
      · rw [agent_payoff_eq, agent_base_eq, condInterim_eq, condInterim_eq,
          dev_h_eq, base_h_eq, t1dev000, t1base00, marg00]
      · rw [agent_payoff_eq, agent_base_eq, condInterim_eq, condInterim_eq,
          dev_h_eq, base_h_eq, t1dev001, t1base00, marg00]
        norm_num
    · rw [Fin.forall_fin_two]
      constructor
      · rw [agent_payoff_eq, agent_base_eq, condInterim_eq, condInterim_eq,
          dev_h_eq, base_h_eq, t1dev010, t1base01, marg01]
      · rw [agent_payoff_eq, agent_base_eq, condInterim_eq, condInterim_eq,
          dev_h_eq, base_h_eq, t1dev011, t1base01, marg01]
        norm_num
  · rw [Fin.forall_fin_two]
    constructor
    · rw [Fin.forall_fin_two]
      constructor
      · rw [agent_payoff_eq, agent_base_eq, condInterim_eq, condInterim_eq,
          dev_h_eq, base_h_eq, t1dev100, t1base10, marg10]
      · rw [agent_payoff_eq, agent_base_eq, condInterim_eq, condInterim_eq,
          dev_h_eq, base_h_eq, t1dev101, t1base10, marg10]
        norm_num
    · rw [Fin.forall_fin_two]
      constructor
      · rw [agent_payoff_eq, agent_base_eq, condInterim_eq, condInterim_eq,
          dev_h_eq, base_h_eq, t1dev110, t1base11, marg11]
        norm_num
      · rw [agent_payoff_eq, agent_base_eq, condInterim_eq, condInterim_eq,
          dev_h_eq, base_h_eq, t1dev111, t1base11, marg11]

/-- The candidate profile is a Nash equilibrium of the agent form. -/
theorem t3_example_agentForm_nash :
    StrategicGame.IsNash exGame.agentForm (agentProfileEquiv sStar) := by
  show ∀ (a : Σ _ : Fin 2, Fin 2) (t : Fin 2),
    exGame.condInterim
      (agentProfileEquiv.symm (Function.update (agentProfileEquiv sStar) a t)) a.fst a.snd ≤
    exGame.condInterim
      (agentProfileEquiv.symm (Function.update (agentProfileEquiv sStar) a
        ((agentProfileEquiv sStar) a))) a.fst a.snd
  intro a t
  obtain ⟨i, θi⟩ := a
  exact t3_all i θi t

/-- The ex-interim characterization, applied to the example equilibrium. -/
theorem t4_example_exInterim_optimal :
    ∀ (i θi a : Fin 2),
      exGame.condInterim (Function.update sStar i (fun _ => a)) i θi ≤
        exGame.condInterim sStar i θi :=
  (isBayesNash_iff exGame sStar).mp t1_example_isBayesNash

/-- The agent-form equivalence, forward direction on the example. -/
theorem t5_example_agentForm_of_bayesNash :
    StrategicGame.IsNash exGame.agentForm (agentProfileEquiv sStar) :=
  (isBayesNash_iff_isNash_agentForm exGame sStar).mp t1_example_isBayesNash

/-- The agent-form equivalence, reverse direction on the example. -/
theorem t6_example_bayesNash_of_agentForm : exGame.IsBayesNash sStar :=
  (isBayesNash_iff_isNash_agentForm exGame sStar).mpr t3_example_agentForm_nash

end MathlibExtTest.GameTheory.BayesianGame
