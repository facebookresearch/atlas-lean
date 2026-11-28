/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Dynamics.PolynomialNetworks.StochasticMassAction

/-! # Stochastic mass-action propensity and firing: examples -/

open MathlibExt.Biology.Dynamics.ComplexBalanced

/-- Test network consuming two copies of the single species. -/
private def dimer : ReactionNetwork Unit Unit where
  src := fun _ _ => 2
  prod := fun _ _ => 0

/-- Test network with immigration of one copy and an empty source. -/
private def immig : ReactionNetwork Unit Unit where
  src := fun _ _ => 0
  prod := fun _ _ => 1

/-- Propensity value with unit rate: `5.descFactorial 2 = 20`. -/
example : dimer.propensity (fun _ => 1) () (fun _ => 5) = 20 := by
  unfold ReactionNetwork.propensity dimer
  norm_num [Nat.descFactorial]

/-- Propensity vanishes when the source does not fit (`propensity_eq_zero_of_not_le`). -/
example : dimer.propensity (fun _ => 1) () (fun _ => 1) = 0 := by
  apply ReactionNetwork.propensity_eq_zero_of_not_le
  intro h
  have h2 := h ()
  simp [dimer] at h2

/-- Propensity is nonnegative for nonnegative rates (`propensity_nonneg`). -/
example (k : Unit → ℝ) (hk : ∀ r, 0 ≤ k r) (x : Unit → ℕ) : 0 ≤ dimer.propensity k () x := by
  exact ReactionNetwork.propensity_nonneg dimer hk () x

/-- Immigration propensity equals the rate constant. -/
example (κ : ℝ) (x : Unit → ℕ) : immig.propensity (fun _ => κ) () x = κ := by
  unfold ReactionNetwork.propensity immig
  simp

/-- Firing removes the source and adds the product. -/
example : dimer.fire () (fun _ => 5) = fun _ => 3 := by
  funext s
  simp [ReactionNetwork.fire, dimer]

/-- Unfiring reverses firing on the test state. -/
example : dimer.unfire () (fun _ => 3) = fun _ => 5 := by
  funext s
  simp [ReactionNetwork.unfire, dimer]
