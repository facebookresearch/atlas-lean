/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Connecting the physical trace computation to the actual involution eigenspace. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTraceFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalProductInvariance

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

private theorem coordinate_as_row (A : Matrix (Fin 24) (Fin 24) ℝ)
    (X : GriessShortIndex → ℝ) :
    centralizerCoordinateTensorMul A X =
      centralizerAlgebraRow (conwayMatrixTensorProduct A) conwayTensorShortOperator X := rfl

private theorem tensorRow_apply {ι : Type*} [Fintype ι]
    (M : (SpinIndex → Fin 24 → ℝ) →ₗ[ℝ] (SpinIndex → Fin 24 → ℝ))
    (P : ι → (SpinIndex → Fin 24 → ℝ) →ₗ[ℝ] (SpinIndex → Fin 24 → ℝ))
    (X : ι → ℝ) (T : SpinIndex → Fin 24 → ℝ) :
    centralizerAlgebraRow M P X T = M T + (1 / 8 : ℝ) • ∑ r, X r • P r T := by
  simp only [centralizerAlgebraRow, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.smul_sum]
  apply congrArg (fun z : SpinIndex → Fin 24 → ℝ => M T + z)
  apply Finset.sum_congr rfl
  intro r _
  rw [smul_smul]
  congr 1
  ring


private theorem tensorRow_zero_right {ι : Type*} [Fintype ι]
    (P : ι → (SpinIndex → Fin 24 → ℝ) →ₗ[ℝ] (SpinIndex → Fin 24 → ℝ)) (X : ι → ℝ) :
    (1 / 8 : ℝ) • ∑ r, X r • P r (0 : SpinIndex → Fin 24 → ℝ) = 0 := by
  simp only [map_zero, smul_zero, Finset.sum_const_zero]

private theorem shortTensor_zero_right (X : GriessShortIndex → ℝ) :
    conwayShortTensorProduct X 0 = 0 := by
  exact tensorRow_zero_right conwayTensorShortOperator X

private theorem rawTensor_zero (A : Matrix (Fin 24) (Fin 24) ℝ)
    (X : GriessShortIndex → ℝ) (T : SpinIndex → Fin 24 → ℝ) :
    (conwayRawProduct (A,(X,0)) (0,(0,T))).2.2 =
      conwayMatrixTensorProduct A T + conwayShortTensorProduct X T := by
  rw [conwayRawProduct_eq_blocks]
  simp only [map_zero, add_zero, shortTensor_zero_right]

private theorem coordinateRow_apply (A : Matrix (Fin 24) (Fin 24) ℝ)
    (X : GriessShortIndex → ℝ) (T : SpinIndex → Fin 24 → ℝ) :
    centralizerCoordinateTensorMul A X T =
      conwayMatrixTensorProduct A T + conwayShortTensorProduct X T := by
  rw [coordinate_as_row]
  rw [show conwayShortTensorProduct X T =
    (1 / 8 : ℝ) • ∑ r, X r • conwayTensorShortOperator r T from rfl]
  exact tensorRow_apply (conwayMatrixTensorProduct A) conwayTensorShortOperator X T

/-- Physical tensor multiplication is exactly restriction of the actual algebra multiplication. -/
theorem generatedCentralTensorMul_coordinates (u : generatedCentralPlus)
    (x : generatedCentralMinus) :
    generatedCentralMinusTensorEquiv (generatedCentralTensorMul u x) =
      centralizerCoordinateTensorMul (griessConwayEncode u.val).1
        (griessConwayEncode u.val).2.1 (generatedCentralMinusTensorEquiv x) := by
  have hu := (mem_generatedCentralPlus_iff_tensor_zero u.val).mp u.property
  have hx := (mem_generatedCentralMinus_iff_matrix_short_zero x.val).mp x.property
  change (griessConwayEncode (griessProd u.val x.val)).2.2 = _
  rw [show generatedCentralMinusTensorEquiv x = (griessConwayEncode x.val).2.2 from rfl]
  rw [griessProd_encode]
  have hup : griessConwayEncode u.val =
      ((griessConwayEncode u.val).1, ((griessConwayEncode u.val).2.1, 0)) := by
    ext <;> simp only [hu]
  have hxp : griessConwayEncode x.val =
      (0, (0, (griessConwayEncode x.val).2.2)) := by
    ext <;> simp only [hx.1, hx.2]
  rw [hup, hxp, rawTensor_zero, coordinateRow_apply]

/-- Exact conjugacy of the restricted actual operator and its physical coordinate expression. -/
theorem generatedCentralTensorMul_coordinate_conjugate (u : generatedCentralPlus) :
    generatedCentralMinusTensorEquiv.conj (generatedCentralTensorMul u) =
      centralizerCoordinateTensorMul (griessConwayEncode u.val).1
        (griessConwayEncode u.val).2.1 := by
  apply LinearMap.ext
  intro x
  change generatedCentralMinusTensorEquiv
      (generatedCentralTensorMul u (generatedCentralMinusTensorEquiv.symm x)) = _
  exact (generatedCentralTensorMul_coordinates u
    (generatedCentralMinusTensorEquiv.symm x)).trans
    (congrArg (centralizerCoordinateTensorMul (griessConwayEncode u.val).1
      (griessConwayEncode u.val).2.1)
      (generatedCentralMinusTensorEquiv.apply_symm_apply x))

/-- Intrinsic trace on the actual negative eigenspace equals the physical source formula. -/
theorem generatedCentralTensorTraceForm_coordinates (u v : generatedCentralPlus) :
    generatedCentralTensorTraceForm u v =
      4096 * (((griessConwayEncode u.val).1.transpose *
        (griessConwayEncode v.val).1.transpose).trace +
        (5 / 8 : ℝ) * (griessConwayEncode u.val).1.trace *
          (griessConwayEncode v.val).1.trace) +
      4608 * ∑ r, (griessConwayEncode u.val).2.1 r *
        (griessConwayEncode v.val).2.1 r := by
  unfold generatedCentralTensorTraceForm
  calc
    _ = LinearMap.trace ℝ _ (generatedCentralMinusTensorEquiv.conj
        ((generatedCentralTensorMul u).comp (generatedCentralTensorMul v))) :=
      (LinearMap.trace_conj' _ generatedCentralMinusTensorEquiv).symm
    _ = _ := by
      rw [LinearEquiv.conj_comp, generatedCentralTensorMul_coordinate_conjugate,
        generatedCentralTensorMul_coordinate_conjugate]
      exact centralizerCoordinateTensorMul_trace_comp _ _ _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
