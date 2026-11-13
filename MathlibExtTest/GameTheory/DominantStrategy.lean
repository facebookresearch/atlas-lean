/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.DominantStrategy
import Mathlib.Tactic

/-! # Tests for `MathlibExt.GameTheory.DominantStrategy`

In the prisoner's dilemma, defecting is strictly dominant, so mutual defection is the unique Nash
equilibrium. -/

open MathlibExt.GameTheory.DominantStrategy

namespace MathlibExtTest.GameTheory.DominantStrategy

def pdPayoff (own opp : Bool) : ℝ :=
  if own then (if opp then 1 else 5) else (if opp then 0 else 3)

def pd : Fin 2 → (Fin 2 → Bool) → ℝ :=
  fun i σ => pdPayoff (σ i) (if i = 0 then σ 1 else σ 0)

theorem pd_defect_isStrictlyDominant (i : Fin 2) : IsStrictlyDominant pd i true := by
  intro τ t ht
  have ht_false : t = false := by
    cases t with
    | false => rfl
    | true => exact absurd rfl ht
  subst ht_false
  simp only [pd]
  have h1 : Function.update τ i false i = false := Function.update_self i false τ
  have h2 : Function.update τ i true i = true := Function.update_self i true τ
  have h3 : (if i = 0 then Function.update τ i false 1 else Function.update τ i false 0)
      = (if i = 0 then τ 1 else τ 0) := by
    by_cases hi : i = 0
    · simp only [ite_eq_left hi]
      exact Function.update_of_ne (by rw [hi]; decide) _ _
    · simp only [ite_eq_right hi]
      exact Function.update_of_ne (Ne.symm hi) _ _
  have h4 : (if i = 0 then Function.update τ i true 1 else Function.update τ i true 0)
      = (if i = 0 then τ 1 else τ 0) := by
    by_cases hi : i = 0
    · simp only [ite_eq_left hi]
      exact Function.update_of_ne (by rw [hi]; decide) _ _
    · simp only [ite_eq_right hi]
      exact Function.update_of_ne (Ne.symm hi) _ _
  rw [h1, h2, h3, h4]
  cases (if i = 0 then τ 1 else τ 0) <;> norm_num [pdPayoff]

theorem pd_allDefect_isNash : IsNash pd (fun _ => true) :=
  isNash_of_isStrictlyDominant (fun i => pd_defect_isStrictlyDominant i)

theorem pd_allCoop_notNash : ¬ IsNash pd (fun _ => false) := by
  intro hNash
  have heq :=
    eq_of_isNash_of_isStrictlyDominant (fun i => pd_defect_isStrictlyDominant i) hNash
  have h0 := congrFun heq 0
  simp at h0

end MathlibExtTest.GameTheory.DominantStrategy
