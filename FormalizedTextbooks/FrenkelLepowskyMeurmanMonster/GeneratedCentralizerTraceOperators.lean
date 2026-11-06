/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact tensor operator traces for the centralizer reconstruction. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SpinLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortBasisProduct

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual Pauli operator tensored with a physical 24-dimensional matrix. -/
noncomputable def centralizerPauliTensor (q : Q) (A : Matrix (Fin 24) (Fin 24) ℝ) :
    (SpinIndex → Fin 24 → ℝ) →ₗ[ℝ] (SpinIndex → Fin 24 → ℝ) :=
  conwayTensorCoordinates.conj
    (TensorProduct.map (spinRepresentation q).toLinearMap A.toLin')

theorem centralizerPauliTensor_trace (q : Q) (A : Matrix (Fin 24) (Fin 24) ℝ) :
    LinearMap.trace ℝ _ (centralizerPauliTensor q A) =
      LinearMap.trace ℝ SpinSpace (spinRepresentation q).toLinearMap * A.trace := by
  rw [centralizerPauliTensor, LinearMap.trace_conj', LinearMap.trace_tensorProduct',
    Matrix.trace_toLin'_eq]

/-- Noncentral Pauli terms have zero tensor trace, independently of the spatial matrix. -/
theorem centralizerPauliTensor_trace_noncentral (q : Q) (hq : q ∉ centerQ)
    (A : Matrix (Fin 24) (Fin 24) ℝ) :
    LinearMap.trace ℝ _ (centralizerPauliTensor q A) = 0 := by
  rw [centralizerPauliTensor_trace, spinRepresentation_trace_noncentral' q hq, zero_mul]

private theorem centralizer_conj_comp {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℝ V] [Module ℝ W] (e : V ≃ₗ[ℝ] W) (a b : V →ₗ[ℝ] V) :
    (e.conj a).comp (e.conj b) = e.conj (a.comp b) := by
  apply LinearMap.ext
  intro x
  change e (a (e.symm (e (b (e.symm x))))) = e (a (b (e.symm x)))
  rw [LinearEquiv.symm_apply_apply]

theorem centralizerPauliTensor_comp (q r : Q)
    (A B : Matrix (Fin 24) (Fin 24) ℝ) :
    (centralizerPauliTensor q A).comp (centralizerPauliTensor r B) =
      centralizerPauliTensor (q * r) (A * B) := by
  unfold centralizerPauliTensor
  rw [centralizer_conj_comp, ← TensorProduct.map_comp]
  apply congrArg conwayTensorCoordinates.conj
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro x
    change spinRepresentation q (spinRepresentation r x) = spinRepresentation (q * r) x
    rw [map_mul]
    rfl
  · apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec]

/-- The actual short-vector spatial coefficient, regarded as a matrix for matrix multiplication. -/
noncomputable def centralizerShortSpatialMatrix (r : GriessShortIndex) :
    Matrix (Fin 24) (Fin 24) ℝ := conwayTensorCoefficient r

/-- The existing actual short operator is exactly this Pauli tensor. -/
theorem conwayTensorShortOperator_eq_pauli (r : GriessShortIndex) :
    conwayTensorShortOperator r = centralizerPauliTensor (griessShortQ r)
      (centralizerShortSpatialMatrix r) := by
  unfold conwayTensorShortOperator centralizerPauliTensor centralizerShortSpatialMatrix
  rw [LinearEquiv.conj_apply, LinearMap.comp_assoc]

theorem conwayTensorShortOperator_trace (r : GriessShortIndex) :
    LinearMap.trace ℝ _ (conwayTensorShortOperator r) = 0 := by
  rw [conwayTensorShortOperator_eq_pauli]
  apply centralizerPauliTensor_trace_noncentral
  intro h
  exact griessShortQ_base_ne_one r ((q_mem_center_iff_base_eq_one _).mp h)

/-- Distinct actual short-vector operators are orthogonal for the tensor trace form. -/
theorem conwayTensorShortOperator_trace_comp_of_ne (r s : GriessShortIndex) (hrs : r ≠ s) :
    LinearMap.trace ℝ _ ((conwayTensorShortOperator r).comp
      (conwayTensorShortOperator s)) = 0 := by
  rw [conwayTensorShortOperator_eq_pauli, conwayTensorShortOperator_eq_pauli,
    centralizerPauliTensor_comp]
  apply centralizerPauliTensor_trace_noncentral
  intro h
  exact hrs ((griessShortQ_product_base_one_iff r s).mp
    ((q_mem_center_iff_base_eq_one _).mp h))

/-- The actual spatial coefficient of a short vector is a rank-one perturbation. -/
theorem conwayTensorCoefficient_eq_rank_one (r : GriessShortIndex) :
    centralizerShortSpatialMatrix r =
      (1 : Matrix (Fin 24) (Fin 24) ℝ) - (2 : ℝ) •
      Matrix.vecMulVec (griessShortVector r) (griessShortVector r) := by
  ext i j
  simp only [centralizerShortSpatialMatrix, conwayTensorCoefficient, Matrix.sub_apply,
    Matrix.one_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

/-- The spatial coefficient's square has the exact source trace 72. -/
theorem conwayTensorCoefficient_trace_square (r : GriessShortIndex) :
    Matrix.trace (centralizerShortSpatialMatrix r *
      centralizerShortSpatialMatrix r) = 72 := by
  have hn : griessShortVector r ⬝ᵥ griessShortVector r = (4 : ℝ) :=
    griessShortVector_norm_sq r
  rw [conwayTensorCoefficient_eq_rank_one]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, hn,
    dotProduct_smul, smul_eq_mul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_vecMulVec]
  simp only [Matrix.trace_one, Fintype.card_fin]
  norm_num

/-- Each actual short operator has squared tensor trace 294912. -/
theorem conwayTensorShortOperator_trace_square (r : GriessShortIndex) :
    LinearMap.trace ℝ _ ((conwayTensorShortOperator r).comp
      (conwayTensorShortOperator r)) = 294912 := by
  rw [conwayTensorShortOperator_eq_pauli, centralizerPauliTensor_comp,
    griessShortQ_square, centralizerPauliTensor_trace,
    conwayTensorCoefficient_trace_square]
  have ht : LinearMap.trace ℝ SpinSpace (spinRepresentation (1 : Q)).toLinearMap = 4096 := by
    rw [← spinCoordinateTrace_eq_trace]
    have hc : qCentral 0 = (1 : Q) := rfl
    simpa only [hc, qSign_zero, mul_one] using spinRepresentation_trace_central 0
  rw [ht]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
