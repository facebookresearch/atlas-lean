/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic



open Finset

noncomputable section


noncomputable def finiteLagrangeBasis
    {α : Type*} [Fintype α] [DecidableEq α]
    (position : α → Complex) (a : α) (z : Complex) : Complex :=
  ∏ b ∈ Finset.univ.erase a, (z - position b) / (position a - position b)


noncomputable def finiteLagrangeInterpolant
    {α : Type*} [Fintype α] [DecidableEq α]
    (position value : α → Complex) (z : Complex) : Complex :=
  ∑ a, value a * finiteLagrangeBasis position a z

theorem finiteLagrangeBasis_self
    {α : Type*} [Fintype α] [DecidableEq α]
    (position : α → Complex) (hposition : Function.Injective position)
    (a : α) :
    finiteLagrangeBasis position a (position a) = 1 := by
  classical
  unfold finiteLagrangeBasis
  apply Finset.prod_eq_one
  intro b hb
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have hne : position a - position b ≠ 0 := sub_ne_zero.mpr (hposition.ne hba.symm)
  exact div_self hne

theorem finiteLagrangeBasis_apply_eq_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    (position : α → Complex) (a b : α) (hab : a ≠ b) :
    finiteLagrangeBasis position b (position a) = 0 := by
  classical
  unfold finiteLagrangeBasis
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩)
  simp

@[simp] theorem finiteLagrangeInterpolant_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (position value : α → Complex) (hposition : Function.Injective position)
    (a : α) :
    finiteLagrangeInterpolant position value (position a) = value a := by
  classical
  unfold finiteLagrangeInterpolant
  rw [Finset.sum_eq_single a]
  · rw [finiteLagrangeBasis_self position hposition]
    simp
  · intro b _hb hba
    rw [finiteLagrangeBasis_apply_eq_zero position a b hba.symm]
    simp
  · simp

theorem differentiable_finiteLagrangeBasis
    {α : Type*} [Fintype α] [DecidableEq α]
    (position : α → Complex) (a : α) :
    Differentiable Complex (finiteLagrangeBasis position a) := by
  classical
  unfold finiteLagrangeBasis
  have h : Differentiable Complex
      (∏ b ∈ Finset.univ.erase a,
        fun z : Complex ↦ (z - position b) / (position a - position b)) := by
    apply Differentiable.finsetProd
    intro b _hb
    fun_prop
  convert h using 1
  ext z
  simp only [Finset.prod_apply]

theorem differentiable_finiteLagrangeInterpolant
    {α : Type*} [Fintype α] [DecidableEq α]
    (position value : α → Complex) :
    Differentiable Complex (finiteLagrangeInterpolant position value) := by
  classical
  unfold finiteLagrangeInterpolant
  have h : Differentiable Complex
      (∑ a : α, fun z : Complex ↦
        value a * finiteLagrangeBasis position a z) := by
    apply Differentiable.sum
    intro a _ha
    exact (differentiable_finiteLagrangeBasis position a).const_mul (value a)
  convert h using 1
  ext z
  simp only [Finset.sum_apply]

end
