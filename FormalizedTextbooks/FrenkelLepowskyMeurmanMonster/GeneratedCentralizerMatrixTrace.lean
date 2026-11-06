/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact matrix constituent contribution to the intrinsic tensor trace. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTraceOperators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- The physical 24-dimensional factor of multiplication by a matrix vector on the tensor space. -/
noncomputable def centralizerMatrixSpatial (A : Matrix (Fin 24) (Fin 24) ℝ) :
    Matrix (Fin 24) (Fin 24) ℝ := A.transpose + (A.trace / 8) • 1

/-- The matrix/tensor row of the actual Conway product is the identity Pauli tensor. -/
theorem conwayMatrixTensorProduct_eq_pauli (A : Matrix (Fin 24) (Fin 24) ℝ) :
    conwayMatrixTensorProduct A = centralizerPauliTensor 1 (centralizerMatrixSpatial A) := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := conwayTensorCoordinates.surjective x
  induction x using TensorProduct.inductionOn with
  | tmul u v =>
    rw [conwayMatrixTensorProduct_tmul]
    simp only [centralizerPauliTensor, LinearEquiv.conj_apply_apply,
      LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, Matrix.toLin'_apply,
      map_one, LinearEquiv.coe_toLinearMap_one, LinearMap.id_apply, centralizerMatrixSpatial,
      Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The exact 24-dimensional trace formula, without irreducibility assumptions. -/
theorem centralizerMatrixSpatial_trace_comp (A B : Matrix (Fin 24) (Fin 24) ℝ) :
    (centralizerMatrixSpatial A * centralizerMatrixSpatial B).trace =
      (A.transpose * B.transpose).trace + (5 / 8 : ℝ) * A.trace * B.trace := by
  simp only [centralizerMatrixSpatial, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_transpose, Matrix.trace_one, Fintype.card_fin]
  norm_num
  ring

/-- The concrete matrix contribution to the full tensor trace form. -/
theorem conwayMatrixTensorProduct_trace_comp (A B : Matrix (Fin 24) (Fin 24) ℝ) :
    LinearMap.trace ℝ _ ((conwayMatrixTensorProduct A).comp (conwayMatrixTensorProduct B)) =
      4096 * ((A.transpose * B.transpose).trace + (5 / 8 : ℝ) * A.trace * B.trace) := by
  rw [conwayMatrixTensorProduct_eq_pauli, conwayMatrixTensorProduct_eq_pauli,
    centralizerPauliTensor_comp, one_mul, centralizerPauliTensor_trace,
    centralizerMatrixSpatial_trace_comp]
  have ht : LinearMap.trace ℝ SpinSpace (spinRepresentation (1 : Q)).toLinearMap = 4096 := by
    rw [← spinCoordinateTrace_eq_trace]
    have hc : qCentral 0 = (1 : Q) := rfl
    simpa only [hc, qSign_zero, mul_one] using spinRepresentation_trace_central 0
  rw [ht]

/-- Actual matrix and short terms have zero mixed tensor trace. -/
theorem conwayMatrixTensorProduct_trace_comp_short (A : Matrix (Fin 24) (Fin 24) ℝ)
    (r : GriessShortIndex) :
    LinearMap.trace ℝ _ ((conwayMatrixTensorProduct A).comp
      (conwayTensorShortOperator r)) = 0 := by
  rw [conwayMatrixTensorProduct_eq_pauli, conwayTensorShortOperator_eq_pauli,
    centralizerPauliTensor_comp, one_mul]
  apply centralizerPauliTensor_trace_noncentral
  intro h
  exact griessShortQ_base_ne_one r ((q_mem_center_iff_base_eq_one _).mp h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
