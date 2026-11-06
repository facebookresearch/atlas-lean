/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual matrix-fixing centralizer acts identically on all spatial tensor columns. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerMatrixTensorAction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Multiplication by an actual pure matrix is its original tensor-coordinate operator. -/
theorem generatedCentralMatrix_tensorMul_coordinates (A : Sym24)
    (x : generatedCentralMinus) :
    generatedCentralMinusTensorEquiv (generatedCentralTensorMul (generatedCentralPlusEmbed A 0) x) =
      conwayMatrixTensorProduct A.val (generatedCentralMinusTensorEquiv x) := by
  have hx := (mem_generatedCentralMinus_iff_matrix_short_zero x.val).mp x.property
  have hxp : griessConwayEncode x.val =
      (0, (0, generatedCentralMinusTensorEquiv x)) := Prod.ext hx.1 (Prod.ext hx.2 rfl)
  change (griessConwayEncode (griessProd (generatedCentralPlusEmbed A 0).val x.val)).2.2 = _
  rw [griessProd_encode, generatedCentralPlusEmbed_encode, hxp,
    generatedCentral_raw_matrix_tensor_product]

/-- The coordinate tensor action intertwines the actual negative-space restriction. -/
theorem generatedCentralizerTensorAction_intertwines (g : generatedCentralizer)
    (x : generatedCentralMinus) :
    generatedCentralizerTensorAction g (generatedCentralMinusTensorEquiv x) =
      generatedCentralMinusTensorEquiv (generatedCentralizerMinusEquiv g x) := by
  change generatedCentralMinusTensorEquiv (generatedCentralizerMinusEquiv g
      (generatedCentralMinusTensorEquiv.symm (generatedCentralMinusTensorEquiv x))) = _
  rw [LinearEquiv.symm_apply_apply]

private theorem matrix_fixed_tensor_commutes (g : generatedCentralizer) (A : Sym24)
    (hfix : g.val.val (generatedCentralPlusEmbed A 0).val =
      (generatedCentralPlusEmbed A 0).val) (x : generatedCentralMinus) :
    generatedCentralizerMinusEquiv g (generatedCentralTensorMul (generatedCentralPlusEmbed A 0) x) =
      generatedCentralTensorMul (generatedCentralPlusEmbed A 0)
        (generatedCentralizerMinusEquiv g x) := by
  have hp : generatedCentralizerPlusEquiv g (generatedCentralPlusEmbed A 0) =
      generatedCentralPlusEmbed A 0 := Subtype.ext hfix
  have h := generatedCentralTensorMul_conjugate g (generatedCentralPlusEmbed A 0)
  rw [hp] at h
  have he := congrArg (fun f => f (generatedCentralizerMinusEquiv g x)) h
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply] at he
  exact he.symm

/-- Fixing every actual matrix vector forces commutation with each Conway matrix tensor operator. -/
theorem generatedCentralizerTensorAction_commutes_matrixTensor (g : generatedCentralizer)
    (hfix : ∀ A : Sym24, g.val.val (generatedCentralPlusEmbed A 0).val =
      (generatedCentralPlusEmbed A 0).val) (A : Sym24) (T : SpinIndex → Fin 24 → ℝ) :
    generatedCentralizerTensorAction g (conwayMatrixTensorProduct A.val T) =
      conwayMatrixTensorProduct A.val (generatedCentralizerTensorAction g T) := by
  obtain ⟨x, rfl⟩ := generatedCentralMinusTensorEquiv.surjective T
  rw [← generatedCentralMatrix_tensorMul_coordinates, generatedCentralizerTensorAction_intertwines,
    matrix_fixed_tensor_commutes g A (hfix A), generatedCentralMatrix_tensorMul_coordinates,
    generatedCentralizerTensorAction_intertwines]

private theorem symmetric_matrix_tensor_formula (A : Matrix (Fin 24) (Fin 24) ℝ)
    (hA : A.IsSymm) (T : SpinIndex → Fin 24 → ℝ) :
    conwayMatrixTensorProduct A T = (fun t => A *ᵥ T t) + (A.trace / 8) • T := by
  funext t i
  rw [conwayMatrixTensorProduct_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  apply congrArg (fun z : ℝ => z + A.trace / 8 * T t i)
  apply Finset.sum_congr rfl
  intro j _
  rw [show A j i = A i j from congrArg (fun B : Matrix (Fin 24) (Fin 24) ℝ => B i j) hA]

/-- The scalar trace correction cancels, leaving commutation with ordinary symmetric matrices. -/
theorem generatedCentralizerTensorAction_commutes_symmetric (g : generatedCentralizer)
    (hfix : ∀ A : Sym24, g.val.val (generatedCentralPlusEmbed A 0).val =
      (generatedCentralPlusEmbed A 0).val) (A : Matrix (Fin 24) (Fin 24) ℝ)
    (hA : A.IsSymm) (T : SpinIndex → Fin 24 → ℝ) :
    generatedCentralizerTensorAction g (fun t => A *ᵥ T t) =
      fun t => A *ᵥ (generatedCentralizerTensorAction g T) t := by
  have h := generatedCentralizerTensorAction_commutes_matrixTensor g hfix ⟨A, hA⟩ T
  change generatedCentralizerTensorAction g (conwayMatrixTensorProduct A T) =
      conwayMatrixTensorProduct A (generatedCentralizerTensorAction g T) at h
  rw [symmetric_matrix_tensor_formula A hA, symmetric_matrix_tensor_formula A hA,
    map_add, map_smul] at h
  exact add_right_cancel h

/-- The genuine matrix-fixing centralizer is one spin operator applied in all 24 tensor columns. -/
theorem generatedCentralizerTensorAction_spin_columns (g : generatedCentralizer)
    (hfix : ∀ A : Sym24, g.val.val (generatedCentralPlusEmbed A 0).val =
      (generatedCentralPlusEmbed A 0).val) :
    ∃ S : Module.End ℝ SpinSpace, ∀ (T : SpinIndex → Fin 24 → ℝ) t i,
      generatedCentralizerTensorAction g T t i = S (fun u => T u i) t := by
  exact tensorMatrixCommutant (generatedCentralizerTensorAction g).toLinearMap
    (generatedCentralizerTensorAction_commutes_symmetric g hfix)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
