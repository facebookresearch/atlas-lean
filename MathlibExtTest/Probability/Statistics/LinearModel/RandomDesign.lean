/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.RandomDesign
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Tests for `MathlibExt.Probability.Statistics.LinearModel.RandomDesign` -/

open Matrix MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.LinearModel

namespace MathlibExtTest.LinearModelRandomDesign

/-! ### The full-rank event and the residual degrees of freedom -/

/-- Intercept-only design with three observations. -/
noncomputable def X₀ : Matrix (Fin 3) (Fin 1) ℝ := Matrix.of fun _ _ => 1

theorem X₀_mem : X₀ ∈ fullRankDesigns (Fin 3) (Fin 1) := by
  have h : X₀ᵀ * X₀ = Matrix.of fun _ _ => 3 := by
    ext i j
    simp [X₀, Matrix.mul_apply]
  change IsUnit (X₀ᵀ * X₀)
  rw [Matrix.isUnit_iff_isUnit_det, h, Matrix.det_unique]
  simp

/-- The intercept design has rank `p = 1`. -/
example : X₀.rank = 1 := by
  simpa using (mem_fullRankDesigns_iff_rank X₀).1 X₀_mem

/-- Residual degrees of freedom `n - rank X = 3 - 1 = 2`. -/
example : (residualMatrix X₀).rank = 2 := by
  rw [rank_residualMatrix_eq_card_sub_rank X₀_mem,
    (mem_fullRankDesigns_iff_rank X₀).1 X₀_mem]
  simp

/-- Boundary: the zero design is not in the full-rank event. -/
example : (0 : Matrix (Fin 3) (Fin 1) ℝ) ∉ fullRankDesigns (Fin 3) (Fin 1) := by
  simp [fullRankDesigns]

example : MeasurableSet (fullRankDesigns (Fin 3) (Fin 1)) := measurableSet_fullRankDesigns

example : Fintype.card (Fin 1) ≤ Fintype.card (Fin 3) :=
  card_le_card_of_mem_fullRankDesigns X₀_mem

/-- The single restriction `C = 1` has an invertible `C (Xᵀ X)⁻¹ Cᵀ`. -/
example : IsUnit ((1 : Matrix (Fin 1) (Fin 1) ℝ) * (X₀ᵀ * X₀)⁻¹ * 1ᵀ) :=
  isUnit_hypothesisGram X₀_mem (by simp)

/-! ### Conditional laws of a function of an independent pair -/

/-- Conditionally on `X = x`, `X + ε` has the law of `x + ε` when `X ⟂ ε`. -/
example (ν ρ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    ∀ᵐ x ∂(ν.prod ρ).map (fun ω => ω.1),
      condDistrib (fun ω : ℝ × ℝ => ω.1 + ω.2) (fun ω => ω.1) (ν.prod ρ) x =
        ((ν.prod ρ).map (fun ω => ω.2)).map (fun e => x + e) :=
  ae_condDistrib_eq_map_of_indepFun (g := fun x e => x + e) measurable_fst.aemeasurable
    measurable_snd.aemeasurable (indepFun_prod (X := id) (Y := id) measurable_id measurable_id)
    (by fun_prop)

/-! ### The product model: an arbitrary design law, independent Gaussian errors -/

/-- The standard Gaussian on `ℝ³`. -/
noncomputable abbrev ρ : Measure (Fin 3 → ℝ) := Measure.pi fun _ : Fin 3 => gaussianReal 0 1

variable (ν : Measure (Matrix (Fin 3) (Fin 1) ℝ)) [IsProbabilityMeasure ν] {σ : ℝ}

/-- In the product model `(X, Z) ~ ν ⊗ N(0, I)` with `ε = σ Z`, the conditional
Gaussian-error hypothesis holds for every design law `ν`. -/
theorem hcond_prod (hσ : 0 < σ) :
    condDistrib (fun ω : Matrix (Fin 3) (Fin 1) ℝ × (Fin 3 → ℝ) => σ⁻¹ • (σ • ω.2))
        (fun ω => ω.1) (ν.prod ρ) =ᵐ[(ν.prod ρ).map (fun ω => ω.1)] Kernel.const _ ρ := by
  have h : (fun ω : Matrix (Fin 3) (Fin 1) ℝ × (Fin 3 → ℝ) => σ⁻¹ • (σ • ω.2)) =
      fun ω => ω.2 := by
    funext ω
    simp [smul_smul, inv_mul_cancel₀ hσ.ne']
  rw [h]
  refine condDistrib_ae_eq_const_of_indepFun measurable_fst.aemeasurable
    (indepFun_prod (X := id) (Y := id) measurable_id measurable_id) ⟨measurable_snd.aemeasurable, ?_⟩
  simp

/-- The conditional-hypothesis unpacking recovers independence and the Gaussian law. -/
example (hσ : 0 < σ) :
    IndepFun (fun ω : Matrix (Fin 3) (Fin 1) ℝ × (Fin 3 → ℝ) => ω.1)
        (fun ω => σ⁻¹ • (σ • ω.2)) (ν.prod ρ) ∧
      HasLaw (fun ω : Matrix (Fin 3) (Fin 1) ℝ × (Fin 3 → ℝ) => σ⁻¹ • (σ • ω.2)) ρ (ν.prod ρ) :=
  indepFun_hasLaw_of_condDistrib_ae_eq_const measurable_fst.aemeasurable
    ((measurable_snd.const_smul σ).const_smul σ⁻¹).aemeasurable (hcond_prod ν hσ)

/-- Conditional law of `β̂` given the design, for every design law `ν`. -/
example (hσ : 0 < σ) (β : Fin 1 → ℝ) :
    ∀ᵐ x ∂(ν.prod ρ).map (fun ω => ω.1), x ∈ fullRankDesigns (Fin 3) (Fin 1) →
      condDistrib (fun ω => WithLp.toLp 2 (olsEstimator ω.1 (ω.1 *ᵥ β + σ • ω.2)))
          (fun ω => ω.1) (ν.prod ρ) x =
        multivariateGaussian (WithLp.toLp 2 β) (σ ^ 2 • (xᵀ * x)⁻¹) :=
  ae_condDistrib_olsEstimator measurable_fst.aemeasurable
    (measurable_snd.const_smul σ).aemeasurable hσ (hcond_prod ν hσ) β

/-- Conditional `χ²_{3-1}` law of `RSS / σ²` given the design. -/
example (hσ : 0 < σ) (β : Fin 1 → ℝ) :
    ∀ᵐ x ∂(ν.prod ρ).map (fun ω => ω.1), x ∈ fullRankDesigns (Fin 3) (Fin 1) →
      condDistrib (fun ω : Matrix (Fin 3) (Fin 1) ℝ × (Fin 3 → ℝ) =>
          (ω.1 *ᵥ β + σ • ω.2 - ω.1 *ᵥ olsEstimator ω.1 (ω.1 *ᵥ β + σ • ω.2)) ⬝ᵥ
            (ω.1 *ᵥ β + σ • ω.2 - ω.1 *ᵥ olsEstimator ω.1 (ω.1 *ᵥ β + σ • ω.2)) / σ ^ 2)
          (fun ω => ω.1) (ν.prod ρ) x =
        chiSquareMeasure (Fintype.card (Fin 3) - Fintype.card (Fin 1)) :=
  ae_condDistrib_rss_div_sq measurable_fst.aemeasurable
    (measurable_snd.const_smul σ).aemeasurable hσ (hcond_prod ν hσ) (by simp) β

/-- Conditional exact `t` coverage of the intercept given the design. -/
example (hσ : 0 < σ) (β : Fin 1 → ℝ) (c : ℝ) :
    ∀ᵐ x ∂(ν.prod ρ).map (fun ω => ω.1), x ∈ fullRankDesigns (Fin 3) (Fin 1) →
      (condDistrib (fun ω : Matrix (Fin 3) (Fin 1) ℝ × (Fin 3 → ℝ) =>
          tStatistic ω.1 ![1] β (ω.1 *ᵥ β + σ • ω.2)) (fun ω => ω.1) (ν.prod ρ) x).real
          {t | |t| ≤ c} =
        (studentTMeasure (Fintype.card (Fin 3) - Fintype.card (Fin 1))).real (Set.Icc (-c) c) :=
  ae_condDistrib_abs_tStatistic_le measurable_fst.aemeasurable
    (measurable_snd.const_smul σ).aemeasurable hσ (hcond_prod ν hσ) (by simp) β (by simp) c

/-- Conditional `F(1, 2)` law of the test of `β = β₀` given the design. -/
example (hσ : 0 < σ) (β : Fin 1 → ℝ) :
    ∀ᵐ x ∂(ν.prod ρ).map (fun ω => ω.1), x ∈ fullRankDesigns (Fin 3) (Fin 1) →
      condDistrib (fun ω : Matrix (Fin 3) (Fin 1) ℝ × (Fin 3 → ℝ) =>
          fStatistic ω.1 (1 : Matrix (Fin 1) (Fin 1) ℝ) β (ω.1 *ᵥ β + σ • ω.2))
          (fun ω => ω.1) (ν.prod ρ) x =
        snedecorFMeasure (Fintype.card (Fin 1)) (Fintype.card (Fin 3) - Fintype.card (Fin 1)) :=
  ae_condDistrib_fStatistic measurable_fst.aemeasurable
    (measurable_snd.const_smul σ).aemeasurable hσ (hcond_prod ν hσ) (by simp) (by simp)
    (by simp) β (one_mulVec β)

/-- `t` statistic on the full-rank event, for every design law `ν`. -/
example (hσ : 0 < σ) (β : Fin 1 → ℝ) (c : ℝ) :
    (ν.prod ρ).real ((fun ω => ω.1) ⁻¹' fullRankDesigns (Fin 3) (Fin 1) ∩
        {ω | tStatistic ω.1 ![1] β (ω.1 *ᵥ β + σ • ω.2) ∈ Set.Icc (-c) c}) =
      (ν.prod ρ).real ((fun ω => ω.1) ⁻¹' fullRankDesigns (Fin 3) (Fin 1)) *
        (studentTMeasure (Fintype.card (Fin 3) - Fintype.card (Fin 1))).real (Set.Icc (-c) c) :=
  measureReal_tStatistic_mem_inter measurable_fst.aemeasurable
    (measurable_snd.const_smul σ).aemeasurable hσ (hcond_prod ν hσ) (by simp) β (by simp)
    measurableSet_Icc

/-- `F` statistic on the full-rank event, for every design law `ν`. -/
example (hσ : 0 < σ) (β : Fin 1 → ℝ) (c : ℝ) :
    (ν.prod ρ).real ((fun ω => ω.1) ⁻¹' fullRankDesigns (Fin 3) (Fin 1) ∩
        {ω | fStatistic ω.1 (1 : Matrix (Fin 1) (Fin 1) ℝ) β (ω.1 *ᵥ β + σ • ω.2) ∈
          Set.Iic c}) =
      (ν.prod ρ).real ((fun ω => ω.1) ⁻¹' fullRankDesigns (Fin 3) (Fin 1)) *
        (snedecorFMeasure (Fintype.card (Fin 1))
          (Fintype.card (Fin 3) - Fintype.card (Fin 1))).real (Set.Iic c) :=
  measureReal_fStatistic_mem_inter measurable_fst.aemeasurable
    (measurable_snd.const_smul σ).aemeasurable hσ (hcond_prod ν hσ) (by simp) (by simp)
    (by simp) β (one_mulVec β) measurableSet_Iic

/-! ### A design that is almost surely of full rank -/

/-- Under the design law `dirac X₀`, the design is a.s. of full rank. -/
theorem ae_fullRank_dirac :
    ∀ᵐ ω ∂(Measure.dirac X₀).prod ρ, (fun ω : Matrix (Fin 3) (Fin 1) ℝ × (Fin 3 → ℝ) => ω.1) ω ∈
      fullRankDesigns (Fin 3) (Fin 1) := by
  refine ae_of_ae_map (p := fun x => x ∈ fullRankDesigns (Fin 3) (Fin 1))
    measurable_fst.aemeasurable ?_
  change ∀ᵐ x ∂(Measure.map Prod.fst ((Measure.dirac X₀).prod ρ)), _
  rw [Measure.map_fst_prod, measure_univ, one_smul]
  exact (ae_dirac_iff (p := fun x => x ∈ fullRankDesigns (Fin 3) (Fin 1))
    measurableSet_fullRankDesigns).2 X₀_mem

/-- Unconditional exact `t` coverage when the design is a.s. of full rank. -/
example (hσ : 0 < σ) (β : Fin 1 → ℝ) (c : ℝ) :
    ((Measure.dirac X₀).prod ρ).real
        {ω | |tStatistic ω.1 ![1] β (ω.1 *ᵥ β + σ • ω.2)| ≤ c} =
      (studentTMeasure (Fintype.card (Fin 3) - Fintype.card (Fin 1))).real (Set.Icc (-c) c) :=
  measureReal_abs_tStatistic_le_of_ae_fullRank measurable_fst.aemeasurable
    (measurable_snd.const_smul σ).aemeasurable hσ (hcond_prod _ hσ) ae_fullRank_dirac
    (by simp) β (by simp) c

/-- Unconditional exact `F` size when the design is a.s. of full rank. -/
example (hσ : 0 < σ) (β : Fin 1 → ℝ) (c : ℝ) :
    ((Measure.dirac X₀).prod ρ).real
        {ω | fStatistic ω.1 (1 : Matrix (Fin 1) (Fin 1) ℝ) β (ω.1 *ᵥ β + σ • ω.2) ∈ Set.Iic c} =
      (snedecorFMeasure (Fintype.card (Fin 1))
        (Fintype.card (Fin 3) - Fintype.card (Fin 1))).real (Set.Iic c) :=
  measureReal_fStatistic_mem_of_ae_fullRank measurable_fst.aemeasurable
    (measurable_snd.const_smul σ).aemeasurable hσ (hcond_prod _ hσ) ae_fullRank_dirac
    (by simp) (by simp) (by simp) β (one_mulVec β) measurableSet_Iic

end MathlibExtTest.LinearModelRandomDesign
