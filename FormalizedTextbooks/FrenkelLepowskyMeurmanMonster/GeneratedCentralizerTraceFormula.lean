/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact physical tensor trace formula for the matrix and short constituents. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerEuclideanTrace

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual multiplication row on physical tensor coordinates. -/
noncomputable def centralizerCoordinateTensorMul (A : Matrix (Fin 24) (Fin 24) ℝ)
    (X : GriessShortIndex → ℝ) :
    (SpinIndex → Fin 24 → ℝ) →ₗ[ℝ] (SpinIndex → Fin 24 → ℝ) :=
  letI : Module ℝ (SpinIndex → Fin 24 → ℝ) := inferInstance
  centralizerAlgebraRow (conwayMatrixTensorProduct A) conwayTensorShortOperator X

private theorem algebraRow_map {E F ι : Type*} [AddCommMonoid E] [AddCommMonoid F]
    [Module ℝ E] [Module ℝ F] [Fintype ι]
    (f : E →ₗ[ℝ] F) (M : E) (P : ι → E) (X : ι → ℝ) :
    f (centralizerAlgebraRow M P X) = centralizerAlgebraRow (f M) (fun i => f (P i)) X := by
  simp only [centralizerAlgebraRow, map_add, map_sum, map_smul]

set_option backward.isDefEq.respectTransparency true in
/-- Euclidean transport changes no multiplication coefficient or operator. -/
theorem centralizerCoordinateTensorMul_euclidean_conjugate
    (A : Matrix (Fin 24) (Fin 24) ℝ) (X : GriessShortIndex → ℝ) :
    centralizerTensorEuclideanEquiv.conj (centralizerCoordinateTensorMul A X) =
      centralizerEuclideanTensorMul A X := by
  have h := algebraRow_map centralizerTensorEuclideanEquiv.conj.toLinearMap
    (conwayMatrixTensorProduct A) conwayTensorShortOperator X
  dsimp only [centralizerCoordinateTensorMul, centralizerEuclideanTensorMul,
    centralizerEuclideanMatrix, centralizerEuclideanShort, LinearEquiv.coe_coe] at h ⊢
  exact h

/-- Exact trace of the complete actual matrix and short-vector multiplication row. -/
theorem centralizerCoordinateTensorMul_trace_comp
    (A B : Matrix (Fin 24) (Fin 24) ℝ) (X Y : GriessShortIndex → ℝ) :
    LinearMap.trace ℝ _ ((centralizerCoordinateTensorMul A X).comp
      (centralizerCoordinateTensorMul B Y)) =
      4096 * ((A.transpose * B.transpose).trace + (5 / 8 : ℝ) * A.trace * B.trace) +
        4608 * ∑ r, X r * Y r := by
  calc
    _ = LinearMap.trace ℝ _ (centralizerTensorEuclideanEquiv.conj
        ((centralizerCoordinateTensorMul A X).comp (centralizerCoordinateTensorMul B Y))) :=
      (LinearMap.trace_conj' _ centralizerTensorEuclideanEquiv).symm
    _ = _ := by
      rw [LinearEquiv.conj_comp, centralizerCoordinateTensorMul_euclidean_conjugate,
        centralizerCoordinateTensorMul_euclidean_conjugate]
      exact centralizerEuclideanTensorMul_trace_comp A B X Y

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
