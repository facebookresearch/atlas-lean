/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.LinearGaussianJointLaw

@[expose] public section

open MathlibExt.InformationTheory.LinearGaussianJointLaw MeasureTheory ProbabilityTheory Matrix

namespace MathlibExtTest.InformationTheory.LinearGaussianJointLaw

/-- The conditional law of the channel output is the noise kernel. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (H : Matrix (Fin 2) (Fin 2) ℝ)
    {R : Matrix (Fin 2) (Fin 2) ℝ} {X : Ω → EuclideanSpace ℝ (Fin 2)}
    {Z : Ω → EuclideanSpace ℝ (Fin 2)} (hX : Measurable X) (hZ : Measurable Z)
    (hind : IndepFun X Z μ) (hZlaw : μ.map Z = multivariateGaussian 0 R) :
    condDistrib (fun ω => toEuclideanLin H (X ω) + Z ω) X μ =ᵐ[μ.map X]
      MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R) :=
  condDistrib_eq_noiseKernel H hX hZ hind hZlaw

/-- A nonzero constant input, the unit vector `e₀`, satisfies the power model with `P = 1`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] :
    PowerConstraint μ (fun _ => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 1 :=
  ⟨zero_le_one, by simp⟩

/-- The power model is not vacuous: the same input violates it at `P = 1 / 2`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] :
    ¬ PowerConstraint μ (fun _ => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (1 / 2) := by
  rintro ⟨-, h⟩
  norm_num at h

/-- Integrability consequences for the constant input: finite second moment, integrable power,
Bochner second moment at most `1`, and an integrable input. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] :
    MemLp (fun _ : Ω => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 2 μ ∧
      Integrable (fun _ : Ω => ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ ^ 2) μ ∧
      ∫ _ω, ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ ^ 2 ∂μ ≤ 1 ∧
      Integrable (fun _ : Ω => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) μ := by
  have h : PowerConstraint μ (fun _ => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 1 :=
    ⟨zero_le_one, by simp⟩
  exact ⟨h.memLp_two aestronglyMeasurable_const, h.integrable_norm_sq aestronglyMeasurable_const,
    h.integral_norm_sq_le aestronglyMeasurable_const, h.integrable aestronglyMeasurable_const⟩

/-- The power model transfers to the input law. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → EuclideanSpace ℝ (Fin 2)}
    (hX : Measurable X) {P : ℝ} (h : PowerConstraint μ X P) : PowerConstraint (μ.map X) id P :=
  (powerConstraint_map_iff hX.aemeasurable).2 h

/-- The law of the constant input `e₀`, a Dirac mass, satisfies the power model with `P = 1`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] :
    PowerConstraint (μ.map fun _ => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) id 1 :=
  (powerConstraint_map_iff measurable_const.aemeasurable).2 ⟨zero_le_one, by simp⟩

/-- Output covariance `H K Hᵀ + R` for a `2 × 3` channel. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (H : Matrix (Fin 2) (Fin 3) ℝ) {R : Matrix (Fin 2) (Fin 2) ℝ} (hR : R.PosDef)
    {X : Ω → EuclideanSpace ℝ (Fin 3)} {Z : Ω → EuclideanSpace ℝ (Fin 2)} (hX : Measurable X)
    (hZ : Measurable Z) (hind : IndepFun X Z μ) (hZlaw : μ.map Z = multivariateGaussian 0 R)
    (hX2 : MemLp X 2 μ) {K : Matrix (Fin 3) (Fin 3) ℝ}
    (hK : ∀ a b, cov[fun ω => X ω a, fun ω => X ω b; μ] = K a b) :
    cov[fun ω => (toEuclideanLin H (X ω) + Z ω) 0,
      fun ω => (toEuclideanLin H (X ω) + Z ω) 1; μ] = (H * K * Hᵀ + R) 0 1 :=
  covariance_output H hR.posSemidef hX hZ hind hZlaw hX2 hK 0 1

/-- Trace identity at the constant input `e₀`: `trace 0 + ‖e₀‖² = E‖e₀‖²`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] :
    (0 : Matrix (Fin 2) (Fin 2) ℝ).trace + ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ ^ 2 =
      ∫ _ω, ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ ^ 2 ∂μ :=
  trace_add_norm_sq_eq_integral_norm_sq (memLp_const _) (by simp) (fun _ _ => by simp)

/-- Second-moment budget at the constant input `e₀` under the power model with `P = 1`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] :
    (0 : Matrix (Fin 2) (Fin 2) ℝ).trace + ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ ^ 2 ≤ 1 :=
  trace_add_norm_sq_le_of_powerConstraint (μ := μ)
    (X := fun _ => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) measurable_const
    ⟨zero_le_one, by simp⟩ (by simp) (fun _ _ => by simp)

/-- The covariance matrix of the constant input, `0`, is positive semidefinite. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] :
    (0 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef :=
  posSemidef_of_covariance (μ := μ) (X := fun _ => EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
    (memLp_const _) (fun _ _ => by simp)

/-- The singular covariance `0` is not positive definite. -/
example : ¬ (0 : Matrix (Fin 2) (Fin 2) ℝ).PosDef := fun h => by
  simpa using h.det_pos

/-- Positive-definite noise keeps the output covariance positive definite for the rank-one
channel `[[1, 1], [0, 0]]` and the singular input covariance `0`. -/
example : ((!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * 0 * (!![1, 1; 0, 0])ᵀ + 1).PosDef :=
  posDef_output_covariance _ PosSemidef.zero PosDef.one

/-- The rank-one channel sends `e₀` to a nonzero mean: its first coordinate is `1`. -/
example : toEuclideanLin (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
    (EuclideanSpace.single 0 1) 0 = 1 := by
  simp [toEuclideanLin, mulVec, dotProduct, Fin.sum_univ_two]

/-- Deterministic input `e₀` (nonzero mean, singular covariance `0`) through the rank-one
channel with noise `N(0, I)`: output mean `H e₀` and output covariance `I`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → EuclideanSpace ℝ (Fin 2)} (hZ : Measurable Z)
    (hZlaw : μ.map Z = multivariateGaussian 0 1) :
    ∫ ω, (toEuclideanLin (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        (EuclideanSpace.single 0 1) + Z ω) ∂μ =
      toEuclideanLin (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) (EuclideanSpace.single 0 1) ∧
    ∀ i j, cov[fun ω => (toEuclideanLin (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        (EuclideanSpace.single 0 1) + Z ω) i,
      fun ω => (toEuclideanLin (!![1, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        (EuclideanSpace.single 0 1) + Z ω) j; μ] = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j :=
  have h := output_moments_of_const_input _ PosSemidef.one hZ hZlaw (EuclideanSpace.single 0 1)
  ⟨h.1, h.2.2⟩

end MathlibExtTest.InformationTheory.LinearGaussianJointLaw
