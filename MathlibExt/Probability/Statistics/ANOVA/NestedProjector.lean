/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.CochranTheorem
public import MathlibExt.Probability.Distributions.CochranIndependence
public import MathlibExt.Probability.Distributions.ChiSquare
public import Mathlib.Probability.HasLaw

/-!
# Nested-projector analysis of variance: incremental and residual laws

For nested fixed subspaces the squared projected response splits into fitted, incremental
and residual sums of squares. Under spherical Gaussian errors with the mean in the smaller
subspace, and with strictly positive increment and residual degrees of freedom, the
incremental and residual scaled squared norms are independent central chi-squares under
`H₀`. (`chiSquareMeasure 0` is the zero measure, not a Dirac law, so the chi-square
conclusions require positive dimensions.)
-/

@[expose] public section

/-! ===== Private helpers for the pinned declarations. -/

namespace ProbabilityTheory

open MeasureTheory Module
open scoped RealInnerProductSpace

/-- The difference of nested projections lies in the orthogonal complement of the smaller
subspace. -/
private theorem nested_increment_mem_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P₀ P₁ : Submodule ℝ E) (hle : P₀ ≤ P₁) (y : E) :
    P₁.starProjection y - P₀.starProjection y ∈ P₀ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro v hv
  have h1 : ⟪P₁.starProjection y, v⟫ = ⟪y, v⟫ := by
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (hle hv)]
  have h2 : ⟪P₀.starProjection y, v⟫ = ⟪y, v⟫ := by
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hv]
  rw [inner_sub_left, h1, h2, sub_self]

/-- Mean/scale reduction: if the projection kills the mean, the scaled squared projected
length of `m + σ • x` equals that of `x`. -/
private theorem nested_norm_sq_div_scale_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Submodule ℝ E) {σ : ℝ} (hσ : 0 < σ) (m x : E) (hm : K.starProjection m = 0) :
    ‖K.starProjection (m + σ • x)‖ ^ 2 / σ ^ 2 = ‖K.starProjection x‖ ^ 2 := by
  have hmap : K.starProjection (m + σ • x) = σ • K.starProjection x := by
    rw [map_add, hm, zero_add, map_smul]
  rw [hmap, norm_smul, Real.norm_of_nonneg hσ.le, div_eq_iff (pow_ne_zero 2 hσ.ne')]
  ring

/-- The squared projected-length function is measurable. -/
private theorem nested_measurable_norm_sq_starProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (K : Submodule ℝ E) : Measurable fun x : E => ‖K.starProjection x‖ ^ 2 :=
  (K.starProjection.continuous.norm.pow 2).measurable

end ProbabilityTheory
/-! ===== Pinned declarations (replace each `sorry` with a proof). -/

namespace ProbabilityTheory

open MeasureTheory Module
open scoped RealInnerProductSpace

/-- **Nested-projector sum-of-squares split**: for nested subspaces `P₀ ≤ P₁`, the squared
projected length splits into fitted plus incremental parts. -/
theorem sum_sq_split_nested {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (P₀ P₁ : Submodule ℝ E) (hle : P₀ ≤ P₁) (y : E) :
    ‖P₁.starProjection y‖ ^ 2 = ‖P₀.starProjection y‖ ^ 2 +
      ‖P₁.starProjection y - P₀.starProjection y‖ ^ 2 := by
  have hort : ⟪P₀.starProjection y, P₁.starProjection y - P₀.starProjection y⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (Submodule.starProjection_apply_mem _ _)
      (nested_increment_mem_orthogonal P₀ P₁ hle y)
  simp only [pow_two]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hort
  rwa [add_sub_cancel] at hpyth

/-- **Increment as a subspace projection**: the difference of the nested projections is the
projection onto the incremental subspace `P₁ ⊓ P₀ᗮ`. -/
theorem increment_projection_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (P₀ P₁ : Submodule ℝ E) (hle : P₀ ≤ P₁) (y : E) :
    (P₁ ⊓ P₀ᗮ).starProjection y = P₁.starProjection y - P₀.starProjection y := by
  have huQ : P₁.starProjection y - P₀.starProjection y ∈ P₁ ⊓ P₀ᗮ :=
    ⟨sub_mem (Submodule.starProjection_apply_mem _ _)
        (hle (Submodule.starProjection_apply_mem _ _)),
      nested_increment_mem_orthogonal P₀ P₁ hle y⟩
  have hyQ : y - (P₁.starProjection y - P₀.starProjection y) ∈ (P₁ ⊓ P₀ᗮ)ᗮ := by
    have h1 : y - P₁.starProjection y ∈ (P₁ ⊓ P₀ᗮ)ᗮ :=
      Submodule.orthogonal_le inf_le_left (Submodule.sub_starProjection_mem_orthogonal _)
    have h2 : P₀.starProjection y ∈ (P₁ ⊓ P₀ᗮ)ᗮ :=
      (Submodule.isOrtho_iff_le.mpr inf_le_right).symm
        (Submodule.starProjection_apply_mem _ _)
    have heq : y - (P₁.starProjection y - P₀.starProjection y)
        = (y - P₁.starProjection y) + P₀.starProjection y := by abel
    rw [heq]
    exact add_mem h1 h2
  have hmem : (P₁ ⊓ P₀ᗮ).starProjection y - (P₁.starProjection y - P₀.starProjection y)
      ∈ (P₁ ⊓ P₀ᗮ) ⊓ (P₁ ⊓ P₀ᗮ)ᗮ := by
    refine ⟨sub_mem (Submodule.starProjection_apply_mem _ _) huQ, ?_⟩
    have heq : (P₁ ⊓ P₀ᗮ).starProjection y - (P₁.starProjection y - P₀.starProjection y)
        = (y - (P₁.starProjection y - P₀.starProjection y))
          - (y - (P₁ ⊓ P₀ᗮ).starProjection y) := by abel
    rw [heq]
    exact sub_mem hyQ (Submodule.sub_starProjection_mem_orthogonal _)
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
  exact sub_eq_zero.mp hmem

/-- **Central chi-square law of the nested increment**: for `Y = m + σ Z` with
`m ∈ range(P₀)`, `σ > 0`, and `Z` standard Gaussian, the scaled squared increment has
central chi-square law with `finrank P₁ - finrank P₀` degrees of freedom, when that
dimension is strictly positive (`hq`). -/
theorem hasLaw_increment_chiSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P₀ P₁ : Submodule ℝ E) (hle : P₀ ≤ P₁)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → E}
    (hZ : HasLaw Z (stdGaussian E) μ) {σ : ℝ} (hσ : 0 < σ) {m : E} (hm : m ∈ P₀)
    (hq : 0 < finrank ℝ P₁ - finrank ℝ P₀) :
    HasLaw (fun ω => ‖(P₁ ⊓ P₀ᗮ).starProjection (m + σ • Z ω)‖ ^ 2 / σ ^ 2)
      (chiSquareMeasure (finrank ℝ P₁ - finrank ℝ P₀)) μ := by
  have hsup : P₀ ⊔ (P₁ ⊓ P₀ᗮ) = P₁ := by
    apply le_antisymm
    · exact sup_le hle inf_le_left
    · intro x hx
      have hx1 : P₁.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
      have hinc := increment_projection_eq P₀ P₁ hle x
      rw [hx1] at hinc
      have hdecomp : x = P₀.starProjection x + (P₁ ⊓ P₀ᗮ).starProjection x := by
        rw [hinc]
        abel
      rw [hdecomp]
      exact add_mem
        ((le_sup_left : P₀ ≤ P₀ ⊔ (P₁ ⊓ P₀ᗮ)) (Submodule.starProjection_apply_mem _ _))
        ((le_sup_right : (P₁ ⊓ P₀ᗮ) ≤ P₀ ⊔ (P₁ ⊓ P₀ᗮ))
          (Submodule.starProjection_apply_mem _ _))
  have hdisj : P₀ ⊓ (P₁ ⊓ P₀ᗮ) = ⊥ := by
    apply le_bot_iff.mp
    calc P₀ ⊓ (P₁ ⊓ P₀ᗮ) ≤ P₀ ⊓ P₀ᗮ := inf_le_inf le_rfl inf_le_right
      _ = ⊥ := Submodule.inf_orthogonal_eq_bot P₀
  have hfin : finrank ℝ ↥(P₁ ⊓ P₀ᗮ) = finrank ℝ P₁ - finrank ℝ P₀ := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P₀ (P₁ ⊓ P₀ᗮ)
    rw [hsup, hdisj] at h
    have h0 : finrank ℝ (⊥ : Submodule ℝ E) = 0 := by simp
    rw [h0, add_zero] at h
    omega
  have hP0Q : P₀ ⟂ (P₁ ⊓ P₀ᗮ) := (Submodule.isOrtho_iff_le.mpr inf_le_right).symm
  have hQm : (P₁ ⊓ P₀ᗮ).starProjection m = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr (hP0Q hm)
  have hfun : (fun ω => ‖(P₁ ⊓ P₀ᗮ).starProjection (m + σ • Z ω)‖ ^ 2 / σ ^ 2)
      = fun ω => (fun x => ‖(P₁ ⊓ P₀ᗮ).starProjection x‖ ^ 2) (Z ω) := by
    funext ω
    exact nested_norm_sq_div_scale_eq _ hσ _ _ hQm
  rw [hfun]
  have hQ : 0 < finrank ℝ ↥(P₁ ⊓ P₀ᗮ) := by rw [hfin]; exact hq
  have hY : HasLaw (fun x => ‖(P₁ ⊓ P₀ᗮ).starProjection x‖ ^ 2)
      (chiSquareMeasure (finrank ℝ ↥(P₁ ⊓ P₀ᗮ))) (stdGaussian E) :=
    { aemeasurable := (nested_measurable_norm_sq_starProjection _).aemeasurable,
      map_eq := stdGaussian_map_norm_sq_starProjection _ hQ }
  rw [hfin] at hY
  exact hY.fun_comp hZ

/-- **Central chi-square law of the residual**: under the same model, with positive
residual degrees of freedom, the scaled squared residual norm is central chi-square.
The mean condition `m ∈ P₀ ≤ P₁` also puts the mean in `range(P₁)`, so centrality holds. -/
theorem hasLaw_residual_chiSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P₀ P₁ : Submodule ℝ E) (hle : P₀ ≤ P₁)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → E}
    (hZ : HasLaw Z (stdGaussian E) μ) {σ : ℝ} (hσ : 0 < σ) {m : E} (hm : m ∈ P₀)
    (hres : 0 < finrank ℝ E - finrank ℝ P₁) :
    HasLaw (fun ω => ‖(P₁ᗮ).starProjection (m + σ • Z ω)‖ ^ 2 / σ ^ 2)
      (chiSquareMeasure (finrank ℝ E - finrank ℝ P₁)) μ := by
  have hfin : finrank ℝ (P₁ᗮ) = finrank ℝ E - finrank ℝ P₁ := by
    have h := Submodule.finrank_add_finrank_orthogonal P₁
    omega
  have hRm : (P₁ᗮ).starProjection m = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero (hle hm)
  have hfun : (fun ω => ‖(P₁ᗮ).starProjection (m + σ • Z ω)‖ ^ 2 / σ ^ 2)
      = fun ω => (fun x => ‖(P₁ᗮ).starProjection x‖ ^ 2) (Z ω) := by
    funext ω
    exact nested_norm_sq_div_scale_eq _ hσ _ _ hRm
  rw [hfun]
  have hR : 0 < finrank ℝ (P₁ᗮ) := by rw [hfin]; exact hres
  have hY : HasLaw (fun x => ‖(P₁ᗮ).starProjection x‖ ^ 2)
      (chiSquareMeasure (finrank ℝ (P₁ᗮ))) (stdGaussian E) :=
    { aemeasurable := (nested_measurable_norm_sq_starProjection _).aemeasurable,
      map_eq := stdGaussian_map_norm_sq_starProjection _ hR }
  rw [hfin] at hY
  exact hY.fun_comp hZ

/-- **Independence of increment and residual**: the scaled squared increment and the
scaled squared residual are independent. The increment and residual subspaces are
pairwise orthogonal, so this is the two-subspace case of the independence law. -/
theorem indepFun_increment_residual {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P₀ P₁ : Submodule ℝ E) (hle : P₀ ≤ P₁)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → E}
    (hZ : HasLaw Z (stdGaussian E) μ) {σ : ℝ} (hσ : 0 < σ) {m : E} (hm : m ∈ P₀) :
    IndepFun (fun ω => ‖(P₁ ⊓ P₀ᗮ).starProjection (m + σ • Z ω)‖ ^ 2 / σ ^ 2)
      (fun ω => ‖(P₁ᗮ).starProjection (m + σ • Z ω)‖ ^ 2 / σ ^ 2) μ := by
  have hP0Q : P₀ ⟂ (P₁ ⊓ P₀ᗮ) := (Submodule.isOrtho_iff_le.mpr inf_le_right).symm
  have hQm : (P₁ ⊓ P₀ᗮ).starProjection m = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr (hP0Q hm)
  have hRm : (P₁ᗮ).starProjection m = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero (hle hm)
  have hF1 : (fun ω => ‖(P₁ ⊓ P₀ᗮ).starProjection (m + σ • Z ω)‖ ^ 2 / σ ^ 2)
      = (fun x => ‖(P₁ ⊓ P₀ᗮ).starProjection x‖ ^ 2) ∘ Z := by
    funext ω
    exact nested_norm_sq_div_scale_eq _ hσ _ _ hQm
  have hF2 : (fun ω => ‖(P₁ᗮ).starProjection (m + σ • Z ω)‖ ^ 2 / σ ^ 2)
      = (fun x => ‖(P₁ᗮ).starProjection x‖ ^ 2) ∘ Z := by
    funext ω
    exact nested_norm_sq_div_scale_eq _ hσ _ _ hRm
  rw [hF1, hF2]
  have hQR : (P₁ ⊓ P₀ᗮ) ⟂ P₁ᗮ :=
    Submodule.isOrtho_iff_le.mpr (inf_le_left.trans (Submodule.le_orthogonal_orthogonal P₁))
  have := hZ.isProbabilityMeasure
  set Kfam : Fin 2 → Submodule ℝ E := ![P₁ ⊓ P₀ᗮ, P₁ᗮ] with hKfam
  have h01 : Kfam 0 = P₁ ⊓ P₀ᗮ := by simp [hKfam]
  have h11 : Kfam 1 = P₁ᗮ := by simp [hKfam]
  have hpair : Pairwise fun k l => Kfam k ⟂ Kfam l := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · change Kfam 0 ⟂ Kfam 1; rw [h01, h11]; exact hQR
    · change Kfam 1 ⟂ Kfam 0; rw [h01, h11]; exact hQR.symm
    · exact absurd rfl hij
  have hindep := iIndepFun_norm_sq_starProjection_stdGaussian Kfam hpair
  have h2 : IndepFun (fun x : E => ‖(Kfam 0).starProjection x‖ ^ 2)
      (fun x : E => ‖(Kfam 1).starProjection x‖ ^ 2) (stdGaussian E) :=
    hindep.indepFun (show (0 : Fin 2) ≠ 1 by decide)
  rw [h01, h11] at h2
  have hmeasQ : Measurable (fun x : E => ‖(P₁ ⊓ P₀ᗮ).starProjection x‖ ^ 2) :=
    nested_measurable_norm_sq_starProjection _
  have hmeasR : Measurable (fun x : E => ‖(P₁ᗮ).starProjection x‖ ^ 2) :=
    nested_measurable_norm_sq_starProjection _
  have hf1 : AEMeasurable ((fun x : E => ‖(P₁ ⊓ P₀ᗮ).starProjection x‖ ^ 2) ∘ Z) μ :=
    hmeasQ.comp_aemeasurable hZ.aemeasurable
  have hf2 : AEMeasurable ((fun x : E => ‖(P₁ᗮ).starProjection x‖ ^ 2) ∘ Z) μ :=
    hmeasR.comp_aemeasurable hZ.aemeasurable
  rw [indepFun_iff_map_prod_eq_prod_map_map hf1 hf2]
  have hP : (fun ω => (((fun x : E => ‖(P₁ ⊓ P₀ᗮ).starProjection x‖ ^ 2) ∘ Z) ω,
        ((fun x : E => ‖(P₁ᗮ).starProjection x‖ ^ 2) ∘ Z) ω))
      = (fun x : E => (‖(P₁ ⊓ P₀ᗮ).starProjection x‖ ^ 2,
        ‖(P₁ᗮ).starProjection x‖ ^ 2)) ∘ Z := rfl
  have hgP : AEMeasurable (fun x : E => (‖(P₁ ⊓ P₀ᗮ).starProjection x‖ ^ 2,
      ‖(P₁ᗮ).starProjection x‖ ^ 2)) (μ.map Z) :=
    (hmeasQ.prodMk hmeasR).aemeasurable
  rw [hP, ← AEMeasurable.map_map_of_aemeasurable hgP hZ.aemeasurable, hZ.map_eq,
    ← AEMeasurable.map_map_of_aemeasurable hmeasQ.aemeasurable hZ.aemeasurable,
    ← AEMeasurable.map_map_of_aemeasurable hmeasR.aemeasurable hZ.aemeasurable, hZ.map_eq]
  exact h2.map_prod_eq_prod_map_map hmeasQ.aemeasurable hmeasR.aemeasurable

end ProbabilityTheory
