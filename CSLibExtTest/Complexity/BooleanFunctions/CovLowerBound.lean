/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.CovLowerBound
public import CSLibExtTest.Complexity.BooleanFunctions.Poincare

/-!
# Tests for the covariance lower bound from revealment

Tests for `CSLibExt.Complexity.BooleanFunctions.CovLowerBound` on `{0, 1}^Bool` at `p = 1/2`,
with the increasing event `andEvent = {ω | ω true ∧ ω false}` computed by `andTree`:

* `coordI` at small inputs and `cov_coordI_mono` for `andEvent` (each coordinate covariance is
  `1/4 · 1/2 = 1/8`), `cov_coordI_nonneg`;
* non-vacuity of `cov_lower_bound` and `cov_lower_bound_div`: every hypothesis is discharged for
  the one-tree family `κ = Unit`, `T = andTree`, `R = reveal`, `c₀ = 1/4`, `D = 1`, and the
  conclusion is the explicit inequality `3/64 ≤ 1/4`;
* a two-tree family (`κ = Bool`, both trees `andTree`), which exercises the factor
  `Fintype.card κ` with `D = 2`;
* `cov_lower_bound_poincare` for the full tree of the `AND` function.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.OSSS.Poincare StatMech.OSSS.CovLowerBound

example : coordI true (fun x : Bool => x) = 1 := by simp [coordI]
example : coordI false (fun x : Bool => x) = 0 := by simp [coordI]

/-- `andEvent` is an increasing event. -/
lemma andEvent_isIncreasing : IsIncreasing andEvent := by
  intro ω ω' hle hω
  simp only [andEvent, Set.mem_ofPred_eq] at hω ⊢
  have h₁ := hle true
  have h₂ := hle false
  rw [hω.1] at h₁
  rw [hω.2] at h₂
  revert h₁ h₂; cases ω' true <;> cases ω' false <;> simp

/-- `andTree` computes the indicator of `andEvent`. -/
lemma andTree_evalR_eq : andTree.evalR = andEvent.indicator (fun _ => (1 : ℝ)) := by
  funext ω
  cases h₁ : ω true <;> cases h₂ : ω false <;>
    simp [andTree, DecisionTree.evalR, DecisionTree.eval, andEvent, h₁, h₂]

/-- The variance of `andEvent` at `p = 1/2` is `3/16`. -/
lemma var_andEvent : var νHalf (andEvent.indicator (fun _ => (1 : ℝ))) = 3 / 16 := by
  rw [← andTree_evalR_eq, var_andTree]

/-- Each coordinate has influence `1/2` on `andEvent` at `p = 1/2`. -/
lemma infl_andEvent (e : Bool) : infl νHalf (andEvent.indicator (fun _ => (1 : ℝ))) e = 1 / 2 := by
  rw [← andTree_evalR_eq, infl_andTree]

/-- Each coordinate indicator has covariance `1/8` with `andEvent` at `p = 1/2`. -/
lemma cov_coordI_andEvent (e : Bool) :
    cov νHalf (coordI e) (andEvent.indicator (fun _ => (1 : ℝ))) = 1 / 8 := by
  rw [cov_coordI_mono νHalf_isProbWeight (andEvent_isIncreasing.indicator_monotone) e,
    infl_andEvent]
  simp [bernoulliWeight]; norm_num

example (e : Bool) : 0 ≤ cov νHalf (coordI e) (andEvent.indicator (fun _ => (1 : ℝ))) :=
  cov_coordI_nonneg νHalf_isProbWeight andEvent_isIncreasing.indicator_monotone e

/-- The site variance `p (1 - p)` at `p = 1/2` is at least `1/4`. -/
lemma siteVar_νHalf (e : Bool) : (1 / 4 : ℝ) ≤ νHalf e true * νHalf e false := by
  simp [bernoulliWeight]; norm_num

/-- Every revealment of `andTree` at `p = 1/2` is at most `1`. -/
lemma reveal_andTree_le_one (e : Bool) : reveal νHalf andTree e ≤ 1 := by
  cases e
  · rw [reveal_andTree_false]; norm_num
  · rw [reveal_andTree_true]

/-- `cov_lower_bound` for the one-tree family `andTree`: `1 · 1/4 · 3/16 ≤ 1 · (1/8 + 1/8)`. -/
example : (3 / 64 : ℝ) ≤ 1 / 4 := by
  have h := cov_lower_bound (κ := Unit) νHalf_isProbWeight andEvent_isIncreasing rfl
    (fun _ => andTree) (fun _ => andTree_evalR_eq) (fun _ e => reveal νHalf andTree e)
    (fun _ _ => le_rfl) (1 / 4) (by norm_num) siteVar_νHalf 1 zero_le_one
    (fun e => by simpa using reveal_andTree_le_one e)
  rw [var_andEvent, Fintype.sum_bool, cov_coordI_andEvent, cov_coordI_andEvent] at h
  norm_num at h ⊢

/-- `cov_lower_bound` for a family of two copies of `andTree`, with `D = 2`. -/
example : (3 / 32 : ℝ) ≤ 1 / 2 := by
  have h := cov_lower_bound (κ := Bool) νHalf_isProbWeight andEvent_isIncreasing rfl
    (fun _ => andTree) (fun _ => andTree_evalR_eq) (fun _ e => reveal νHalf andTree e)
    (fun _ _ => le_rfl) (1 / 4) (by norm_num) siteVar_νHalf 2 zero_le_two
    (fun e => by
      rw [Fintype.sum_bool]
      linarith [reveal_andTree_le_one e])
  rw [var_andEvent, Fintype.sum_bool, cov_coordI_andEvent, cov_coordI_andEvent] at h
  norm_num at h ⊢

example : ((Fintype.card Unit : ℝ) * (1 / 4) / 1) * var νHalf (andEvent.indicator fun _ => 1)
    ≤ ∑ e, cov νHalf (coordI e) (andEvent.indicator fun _ => 1) :=
  cov_lower_bound_div (κ := Unit) νHalf_isProbWeight andEvent_isIncreasing rfl
    (fun _ => andTree) (fun _ => andTree_evalR_eq) (fun _ e => reveal νHalf andTree e)
    (fun _ _ => le_rfl) (1 / 4) (by norm_num) siteVar_νHalf 1 zero_lt_one
    (fun e => by simpa using reveal_andTree_le_one e)

/-- The full decision tree of `andFun` computes the indicator of `andEvent`. -/
lemma fullTreeUniv_andFun_evalR :
    (fullTreeUniv andFun).evalR = andEvent.indicator (fun _ => (1 : ℝ)) := by
  funext ω
  simp only [DecisionTree.evalR, eval_fullTreeUniv]
  cases h₁ : ω true <;> cases h₂ : ω false <;>
    simp [andFun, andEvent, h₁, h₂]

/-- `cov_lower_bound_poincare` for the full tree of `AND`: `1/4 · 3/16 ≤ 1/4`. -/
example : (1 / 4 : ℝ) * (3 / 16) ≤ 1 / 4 := by
  have h := cov_lower_bound_poincare νHalf_isProbWeight andEvent_isIncreasing andFun
    fullTreeUniv_andFun_evalR (1 / 4) (by norm_num) siteVar_νHalf
  rw [var_andEvent, Fintype.sum_bool, cov_coordI_andEvent, cov_coordI_andEvent] at h
  linarith

end StatMechTest.BooleanFunctions
