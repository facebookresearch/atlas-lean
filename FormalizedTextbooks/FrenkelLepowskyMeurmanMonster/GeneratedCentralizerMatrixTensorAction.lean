/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine residual centralizer commutes with the full spatial matrix action. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerMatrixProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TensorMatrixCommutant

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Conway's pure matrix by pure tensor product is its actual matrix tensor operator. -/
theorem generatedCentral_raw_matrix_tensor_product (A : Matrix (Fin 24) (Fin 24) ℝ)
    (T : SpinIndex → Fin 24 → ℝ) :
    conwayRawProduct (A, (0, 0)) (0, (0, T)) =
      (0, (0, conwayMatrixTensorProduct A T)) := by
  apply Prod.ext
  · funext i j
    simp only [conwayRawProduct, Pi.zero_apply, Matrix.zero_apply, zero_mul, mul_zero,
      add_zero, ite_self, Finset.sum_const_zero, zero_div]
  · apply Prod.ext
    · funext r
      simp only [conwayRawProduct, Pi.zero_apply, Matrix.zero_apply, zero_mul, mul_zero,
        add_zero, ite_self, Finset.sum_const_zero, zero_div,
        show (fun _ : SpinIndex => (0 : ℝ)) = 0 from rfl, map_zero]
    · funext t i
      change (conwayRawProduct (A, (0, 0)) (0, (0, T))).2.2 t i =
        conwayMatrixTensorProduct A T t i
      rw [conwayMatrixTensorProduct_apply]
      simp only [conwayRawProduct, Pi.zero_apply, Matrix.zero_apply, zero_mul, mul_zero,
        add_zero, zero_add, ite_self, Finset.sum_const_zero, zero_div, Matrix.trace_zero]

/-- The actual tensor action of a centralizer element in the original tensor coordinates. -/
noncomputable def generatedCentralizerTensorAction (g : generatedCentralizer) :
    (SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ) :=
  generatedCentralMinusTensorEquiv.symm.trans
    ((generatedCentralizerMinusEquiv g).trans generatedCentralMinusTensorEquiv)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
