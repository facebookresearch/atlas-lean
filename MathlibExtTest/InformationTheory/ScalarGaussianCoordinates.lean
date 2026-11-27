/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ScalarGaussianCoordinates
public import MathlibExt.InformationTheory.ReferenceOutputKL

@[expose] public section

open MathlibExt.InformationTheory.ScalarGaussianCoordinates
open MathlibExt.InformationTheory.LinearGaussianJointLaw MeasureTheory ProbabilityTheory
open InformationTheory MathlibExt.InformationTheory.ReferenceOutputKL
open MathlibExt.Analysis.InnerProductSpace.LineIsometry

namespace MathlibExtTest.InformationTheory.ScalarGaussianCoordinates

/-- The embedding at `2` has sole coordinate `2`, and the projection reads it back. -/
example : scalarCoord 2 0 = 2 ∧ scalarCoordInv (scalarCoord 2) = 2 :=
  ⟨lineIsometry_apply 2 0, scalarCoordInv_scalarCoord 2⟩

/-- The scalar coordinates are the bundled isometry `lineIsometry` and its inverse, which reads
the sole coordinate. -/
example (x : ℝ) (y : EuclideanSpace ℝ (Fin 1)) :
    scalarCoord x = lineIsometry x ∧ scalarCoordInv y = y 0 :=
  ⟨rfl, lineIsometry_symm_apply y⟩

/-- The bundled isometry API applies to the scalar coordinates directly: distances are kept. -/
example (x y : ℝ) : dist (scalarCoord x) (scalarCoord y) = dist x y :=
  lineIsometry.dist_map x y

/-- The noise law `N(0, 2)` embeds as the one-dimensional multivariate Gaussian `N(0, [2])`. -/
example :
    (gaussianReal 0 ⟨2, by norm_num⟩).map scalarCoord =
      multivariateGaussian 0 (!![2] : Matrix (Fin 1) (Fin 1) ℝ) := by
  have h0 : scalarCoord 0 = 0 := map_zero lineIsometry
  have h := map_scalarCoord_gaussianReal 0 2 (by norm_num)
  rwa [h0] at h

/-- Embedding independent Gaussians `N(1, 2) ⊗ N(0, 3)` keeps their mutual information at `0`. -/
example :
    measureMutualInformation
      (ProbabilityMeasure.map
        (⟨(gaussianReal 1 2).prod (gaussianReal 0 3), inferInstance⟩ : ProbabilityMeasure (ℝ × ℝ))
        (Prod.map scalarCoord scalarCoord)) = 0 :=
  (measureMutualInformation_map_scalarCoordPair _).trans
    (measureMutualInformation_prod_eq_zero _ _)

/-- Embedding the diagonal image `x ↦ (x, x)` of `N(0, 1)` keeps its mutual information at `⊤`. -/
example :
    measureMutualInformation
      (diagonalGaussian.map
        (Prod.map scalarCoord scalarCoord)) = ⊤ := by
  rw [measureMutualInformation_map_scalarCoordPair]
  exact measureMutualInformation_diagonalGaussian_eq_top

/-- Chain rule in scalar coordinates with a shared kernel: the conditional term vanishes, so the
embedded joint divergence equals the embedded input divergence. -/
example (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (κ : Kernel ℝ ℝ)
    [IsMarkovKernel κ] :
    klDiv ((μ ⊗ₘ κ).map (Prod.map scalarCoord scalarCoord))
        ((ν ⊗ₘ κ).map (Prod.map scalarCoord scalarCoord)) =
      klDiv (μ.map scalarCoord) (ν.map scalarCoord) := by
  rw [klDiv_map_scalarCoordPair_compProd_eq_add, klDiv_self, add_zero]

/-- Reference-output chain rule in scalar coordinates: among embedded output references, the
embedded true output marginal gives the smallest divergence. -/
example (μ : ProbabilityMeasure (ℝ × ℝ)) (Q : Measure ℝ) [IsProbabilityMeasure Q] :
    klDiv ((μ : Measure (ℝ × ℝ)).map (Prod.map scalarCoord scalarCoord))
        ((((μ : Measure (ℝ × ℝ)).map Prod.fst).map scalarCoord).prod
          (((μ : Measure (ℝ × ℝ)).map Prod.snd).map scalarCoord)) ≤
      klDiv ((μ : Measure (ℝ × ℝ)).map (Prod.map scalarCoord scalarCoord))
        ((((μ : Measure (ℝ × ℝ)).map Prod.fst).map scalarCoord).prod (Q.map scalarCoord)) := by
  rw [klDiv_map_scalarCoordPair_prod_reference_eq_add μ Q]
  exact le_self_add

/-- The input `N(1, 2)` embeds into the vector power model at `P = 1 ^ 2 + 2 = 3`. -/
example :
    PowerConstraint (gaussianReal 1 ⟨2, by norm_num⟩) (fun x => scalarCoord (id x)) 3 := by
  have h := scalarPowerBound_gaussianReal 1 2 (by norm_num)
  norm_num at h
  exact (scalarPowerBound_iff_powerConstraint _ _ _).2 h

/-- The input `N(1, 2)` has a finite second moment, from its scalar power bound at `P = 3`. -/
example : MemLp id 2 (gaussianReal 1 ⟨2, by norm_num⟩) := by
  have h := scalarPowerBound_gaussianReal 1 2 (by norm_num)
  norm_num at h
  exact memLp_of_scalarPowerBound h aestronglyMeasurable_id

/-- The constant input `2` fails the vector power model at `P = 0`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] :
    ¬ PowerConstraint μ (fun _ => scalarCoord 2) 0 := by
  rw [scalarPowerBound_iff_powerConstraint μ (fun _ => 2) 0]
  exact not_scalarPowerBound_zero_const (μ := μ) (by norm_num)

/-- Negative-budget boundary: the zero input fails the scalar power bound at `P = -1`, where
`ENNReal.ofReal` alone would compare `0 ≤ 0`, and so fails the vector power model there too. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} :
    ¬ scalarPowerBound μ (fun _ => (0 : ℝ)) (-1) ∧
      ¬ PowerConstraint μ (fun _ => scalarCoord 0) (-1) := by
  refine ⟨not_scalarPowerBound_of_neg (by norm_num), ?_⟩
  rw [scalarPowerBound_iff_powerConstraint μ (fun _ => 0) (-1)]
  exact not_scalarPowerBound_of_neg (by norm_num)

/-- The scalar divergence `KL(N(0, 1) ‖ N(0, 2))` is the vector closed form at dimension one,
`(log 2 - 1 + 1 / 2) / 2`. -/
example :
    klDiv (gaussianReal 0 ⟨1, zero_lt_one.le⟩) (gaussianReal 0 ⟨2, zero_lt_two.le⟩) =
      ENNReal.ofReal ((Real.log 2 - 1 + 1 / 2) / 2) := by
  have hcoord : ∀ m : ℝ, scalarCoord m = WithLp.toLp 2 ![m] := fun m => by
    ext i
    fin_cases i
    simp
  rw [scalarGaussian_klDiv_eq_vector 0 0 1 2 zero_lt_one zero_lt_two, hcoord,
    MathlibExt.InformationTheory.VectorGaussianKL.multivariateGaussianKLReal_fin_one]
  norm_num

end MathlibExtTest.InformationTheory.ScalarGaussianCoordinates
