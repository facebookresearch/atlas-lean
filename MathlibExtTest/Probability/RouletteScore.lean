/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RouletteScore
import Mathlib.Tactic

@[expose] public section

namespace RussianRoulette

/-- At level `0` the sampled-score contribution is the emission value. -/
example {S : Type*} [Fintype S] [DecidableEq S] (T Q : S → S → ℝ)
    (hsupp : ∀ a b : S, Q a b = 0 → T a b = 0) (E : S → ℝ) (i : S) :
    (∑ x : Fin (0 + 1) → S,
      if x 0 = i then survivalWeight Q x * ratioWeight T Q x * E (x (Fin.last 0))
      else 0)
      = E i := by
  rw [sum_prefixContribution_eq_pow_mulVec T Q hsupp E i 0]
  simp

/-- One-state target kernel. -/
noncomputable def Tone : Fin 1 → Fin 1 → ℝ := fun _ _ => 1 / 2

/-- One-state survival kernel. -/
noncomputable def Qone : Fin 1 → Fin 1 → ℝ := fun _ _ => 1 / 4

/-- One-state emission. -/
def Eone : Fin 1 → ℝ := fun _ => 3

/-- Support hypothesis for the one-state model. -/
theorem hsupp_one : ∀ a b : Fin 1, Qone a b = 0 → Tone a b = 0 := by
  intro a b h
  simp only [Qone] at h
  norm_num at h

/-- Level-2 contribution of the one-state model: `(1 / 2) ^ 2 * 3 = 3 / 4`. -/
example : (∑ x : Fin (2 + 1) → Fin 1,
      if x 0 = 0 then
        survivalWeight Qone x * ratioWeight Tone Qone x * Eone (x (Fin.last 2))
      else 0)
      = 3 / 4 := by
  rw [sum_prefixContribution_eq_pow_mulVec Tone Qone hsupp_one Eone 0 2]
  simp only [pow_two, Matrix.mul_apply, Matrix.mulVec_apply_eq_sum, Matrix.of_apply,
    Fin.sum_univ_one, Tone, Eone]
  norm_num

/-- Two-state nilpotent target kernel: `T 0 1 = 2`, zero elsewhere. -/
def Tnil : Fin 2 → Fin 2 → ℝ
  | 0, 1 => 2
  | _, _ => 0

/-- Two-state conditional next-state kernel. -/
def Pnil : Fin 2 → Fin 2 → ℝ
  | 0, 1 => 1
  | 1, 1 => 1
  | _, _ => 0

/-- Constant stop probability for the nilpotent scene. -/
noncomputable def qnil : Fin 2 → ℝ := fun _ => 1 / 2

/-- Survival kernel for the nilpotent scene. -/
noncomputable def Qnil : Fin 2 → Fin 2 → ℝ := stepKernel qnil Pnil

/-- Constant emission for the nilpotent scene. -/
def Enil : Fin 2 → ℝ := fun _ => 1

/-- Support hypothesis for the nilpotent scene. -/
theorem hsupp_nil : ∀ a b : Fin 2, Qnil a b = 0 → Tnil a b = 0 := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all only [Tnil, Qnil, stepKernel, qnil, Pnil]
  norm_num at h

/-- Level-1 contribution from `0` in the nilpotent scene is `2`. -/
example : (∑ x : Fin (1 + 1) → Fin 2,
      if x 0 = 0 then
        survivalWeight Qnil x * ratioWeight Tnil Qnil x * Enil (x (Fin.last 1))
      else 0)
      = 2 := by
  rw [sum_prefixContribution_eq_pow_mulVec Tnil Qnil hsupp_nil Enil 0 1]
  simp only [pow_one, Matrix.mulVec_apply_eq_sum, Matrix.of_apply, Fin.sum_univ_two,
    Tnil, Enil]
  norm_num

/-- Level-2 contribution from `0` in the nilpotent scene is `0`. -/
example : (∑ x : Fin (2 + 1) → Fin 2,
      if x 0 = 0 then
        survivalWeight Qnil x * ratioWeight Tnil Qnil x * Enil (x (Fin.last 2))
      else 0)
      = 0 := by
  rw [sum_prefixContribution_eq_pow_mulVec Tnil Qnil hsupp_nil Enil 0 2]
  simp only [pow_two, Matrix.mul_apply, Matrix.mulVec_apply_eq_sum, Matrix.of_apply,
    Fin.sum_univ_two, Tnil, Enil]
  norm_num

end RussianRoulette

end
public section
