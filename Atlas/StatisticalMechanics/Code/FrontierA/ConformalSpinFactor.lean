/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Mathlib

open scoped BigOperators

namespace StatMech.FrontierA


noncomputable def isingSpinScalingDimension : ℝ := 1 / 8



noncomputable def spinDerivativeFactor {ι : Type*} [Fintype ι] (d : ι → ℂ) : ℝ :=
  ∏ i, ‖d i‖ ^ isingSpinScalingDimension



noncomputable def spinConformalFactor {ι : Type*} [Fintype ι]
    (Φ : ℂ → ℂ) (a : ι → ℂ) : ℝ :=
  spinDerivativeFactor fun i => deriv Φ (a i)



theorem spinDerivativeFactor_mul {ι : Type*} [Fintype ι]
    (d₁ d₂ : ι → ℂ) :
    spinDerivativeFactor (fun i => d₁ i * d₂ i) =
      spinDerivativeFactor d₁ * spinDerivativeFactor d₂ := by
  classical
  unfold spinDerivativeFactor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]



theorem spinDerivativeFactor_pos {ι : Type*} [Fintype ι]
    {d : ι → ℂ} (hd : ∀ i, d i ≠ 0) : 0 < spinDerivativeFactor d := by
  classical
  unfold spinDerivativeFactor
  apply Finset.prod_pos
  intro i _
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (hd i)) _


@[simp] theorem spinConformalFactor_id {ι : Type*} [Fintype ι]
    (a : ι → ℂ) : spinConformalFactor id a = 1 := by
  classical
  simp [spinConformalFactor, spinDerivativeFactor, deriv_id]








theorem spinConformalFactor_comp {ι : Type*} [Fintype ι]
    (Ψ Φ : ℂ → ℂ) (a : ι → ℂ)
    (hΦ : ∀ i, DifferentiableAt ℂ Φ (a i))
    (hΨ : ∀ i, DifferentiableAt ℂ Ψ (Φ (a i))) :
    spinConformalFactor (Ψ ∘ Φ) a =
      spinConformalFactor Ψ (Φ ∘ a) * spinConformalFactor Φ a := by
  have hderiv : (fun i => deriv (Ψ ∘ Φ) (a i)) =
      fun i => deriv Ψ (Φ (a i)) * deriv Φ (a i) := by
    funext i
    exact ((hΨ i).hasDerivAt.comp (a i) (hΦ i).hasDerivAt).deriv
  unfold spinConformalFactor
  rw [hderiv]
  exact spinDerivativeFactor_mul _ _



theorem spinConformalFactor_pos {ι : Type*} [Fintype ι]
    {Φ : ℂ → ℂ} {a : ι → ℂ} (hΦ : ∀ i, deriv Φ (a i) ≠ 0) :
    0 < spinConformalFactor Φ a :=
  spinDerivativeFactor_pos hΦ

end StatMech.FrontierA
