/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.GramRepresentationLaws
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.L1Translation
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.MaximalSeminorm
public import MathlibExt.Analysis.CStarAlgebra.PointNormAction.CovariantRepresentation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Actual strongly continuous covariant operators of an admissible Gram model

For an actual L1-bounded source seminorm, compact coefficient translation
continuity controls every original-source Gram generator. Their span has
continuous orbits at the group identity. Density and the proved group
isometry then give continuity on every Hilbert vector. The actual group
composition shifts this continuity to every group element.

The computed coefficient and unitary homomorphisms therefore construct a
strongly continuous covariant representation on the actual essential
Hilbert space. No orbit continuity, unitary law, covariance or desired
covariant model is supplied as an input. The original integrated identity
and its maximal-norm consequence remain separate prerequisites.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory
open scoped CStarAlgebra InnerProductSpace Topology

namespace HaarTwistedCore

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
  (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α)) (H : Type uH)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (ρ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- The actual generator orbit difference is controlled by the original Haar L1 translate distance. -/
theorem dist_gramGroupOperator_generator_le
    (hp : p ∈ admissibleCStarSeminorms μ α) (g : G) (f : Carrier μ α) (ξ : ρ.essentialSpace) :
    dist (gramGroupOperator μ α p H ρ g
        (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ))
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) ≤
      l1Gauge μ α (groupLeft μ α g f - f) * ‖ξ‖ := by
  rw [dist_eq_norm, gramGroupOperator_apply_generator]
  have hDiff :
      ρ.essentialRepresentation (p.toNonUnitalCompletion (groupLeft μ α g f)) ξ -
        ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ =
      ρ.essentialRepresentation (p.toNonUnitalCompletion (groupLeft μ α g f - f)) ξ := by
    rw [map_sub, map_sub]
    rfl
  rw [hDiff]
  calc
    _ ≤ ‖ρ.essentialRepresentation (p.toNonUnitalCompletion (groupLeft μ α g f - f))‖ * ‖ξ‖ :=
      (ρ.essentialRepresentation (p.toNonUnitalCompletion (groupLeft μ α g f - f))).le_opNorm ξ
    _ ≤ ‖p.toNonUnitalCompletion (groupLeft μ α g f - f)‖ * ‖ξ‖ :=
      mul_le_mul_of_nonneg_right
        (NonUnitalStarAlgHom.norm_apply_le ρ.essentialRepresentation _) (norm_nonneg ξ)
    _ = p (groupLeft μ α g f - f) * ‖ξ‖ := by rw [p.norm_toNonUnitalCompletion]
    _ ≤ l1Gauge μ α (groupLeft μ α g f - f) * ‖ξ‖ :=
      mul_le_mul_of_nonneg_right (hp _) (norm_nonneg ξ)

/-- Every actual original-source generator has a continuous group orbit at the identity. -/
theorem gramGroupOperator_generator_continuousAt_one
    (hp : p ∈ admissibleCStarSeminorms μ α) (f : Carrier μ α) (ξ : ρ.essentialSpace) :
    ContinuousAt (fun g : G => gramGroupOperator μ α p H ρ g
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ)) 1 := by
  have hL1 : Tendsto (fun g : G => l1Gauge μ α (groupLeft μ α g f - f) * ‖ξ‖)
      (𝓝 1) (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_l1Gauge_groupLeft_sub μ α f).mul_const ‖ξ‖
  change Tendsto _ (𝓝 1)
    (𝓝 (gramGroupOperator μ α p H ρ 1 (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ)))
  rw [gramGroupOperator_one]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hL1.eventually (gt_mem_nhds hε)] with g hg
  exact (dist_gramGroupOperator_generator_le μ α p H ρ hp g f ξ).trans_lt hg

/-- Every vector in the actual original-source Gram span has a continuous orbit at the identity. -/
theorem gramGroupOperator_span_continuousAt_one
    (hp : p ∈ admissibleCStarSeminorms μ α) (ξ : ρ.essentialSpace)
    (hξ : ξ ∈ p.rawHilbertGramDomain H ρ) :
    ContinuousAt (fun g : G => gramGroupOperator μ α p H ρ g ξ) 1 := by
  induction hξ using Submodule.span_induction with
  | mem ξ hξ =>
    obtain ⟨⟨f, η⟩, rfl⟩ := hξ
    exact gramGroupOperator_generator_continuousAt_one μ α p H ρ hp f η
  | zero =>
    simpa only [map_zero] using
      (continuousAt_const : ContinuousAt (fun _ : G => (0 : ρ.essentialSpace)) 1)
  | add ξ η _ _ hξ hη =>
    have hSum := hξ.add hη
    have hFun : ((fun g : G => gramGroupOperator μ α p H ρ g ξ) +
        fun g : G => gramGroupOperator μ α p H ρ g η) =
        fun g : G => gramGroupOperator μ α p H ρ g (ξ + η) := by
      funext g
      rw [Pi.add_apply]
      exact (map_add (gramGroupOperator μ α p H ρ g) ξ η).symm
    rw [hFun] at hSum
    exact hSum
  | smul c ξ _ hξ =>
    have hSmul := hξ.const_smul c
    have hFun : (c • fun g : G => gramGroupOperator μ α p H ρ g ξ) =
        fun g : G => gramGroupOperator μ α p H ρ g (c • ξ) := by
      funext g
      rw [Pi.smul_apply]
      exact (map_smul (gramGroupOperator μ α p H ρ g) c ξ).symm
    rw [hFun] at hSmul
    exact hSmul

/-- Proved density and group isometry make every actual Hilbert-vector orbit continuous at one. -/
theorem gramGroupOperator_continuousAt_one
    (hp : p ∈ admissibleCStarSeminorms μ α) (ξ : ρ.essentialSpace) :
    ContinuousAt (fun g : G => gramGroupOperator μ α p H ρ g ξ) 1 := by
  change Tendsto _ (𝓝 1) (𝓝 (gramGroupOperator μ α p H ρ 1 ξ))
  rw [gramGroupOperator_one]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hεthird : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨η, hη, hApprox⟩ := (p.dense_rawHilbertGramDomain H ρ).exists_dist_lt ξ hεthird
  have hηtendsto : Tendsto (fun g : G => gramGroupOperator μ α p H ρ g η) (𝓝 1) (𝓝 η) := by
    have h := gramGroupOperator_span_continuousAt_one μ α p H ρ hp η hη
    change Tendsto _ (𝓝 1) (𝓝 (gramGroupOperator μ α p H ρ 1 η)) at h
    rw [gramGroupOperator_one] at h
    exact h
  filter_upwards [Metric.tendsto_nhds.mp hηtendsto (ε / 3) hεthird] with g hg
  have hDist : dist (gramGroupOperator μ α p H ρ g ξ) (gramGroupOperator μ α p H ρ g η) =
      dist ξ η := by
    simpa only [dist_eq_norm, map_sub] using norm_gramGroupOperator_apply μ α p H ρ g (ξ - η)
  calc
    dist (gramGroupOperator μ α p H ρ g ξ) ξ ≤
        dist (gramGroupOperator μ α p H ρ g ξ) (gramGroupOperator μ α p H ρ g η) +
          dist (gramGroupOperator μ α p H ρ g η) ξ := dist_triangle _ _ _
    _ ≤ dist ξ η + (dist (gramGroupOperator μ α p H ρ g η) η + dist η ξ) := by
      rw [hDist]
      exact add_le_add (le_refl (dist ξ η))
        (dist_triangle (gramGroupOperator μ α p H ρ g η) η ξ)
    _ < ε / 3 + (ε / 3 + ε / 3) :=
      add_lt_add hApprox (add_lt_add hg (by simpa only [dist_comm] using hApprox))
    _ = ε := by ring

/-- Actual group composition shifts the proved orbit continuity from one to every group element. -/
theorem gramGroupOperator_continuous
    (hp : p ∈ admissibleCStarSeminorms μ α) (ξ : ρ.essentialSpace) :
    Continuous (fun g : G => gramGroupOperator μ α p H ρ g ξ) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  have hAtOne : Tendsto (fun g : G => gramGroupOperator μ α p H ρ g ξ) (𝓝 1) (𝓝 ξ) := by
    have h := gramGroupOperator_continuousAt_one μ α p H ρ hp ξ
    change Tendsto _ (𝓝 1) (𝓝 (gramGroupOperator μ α p H ρ 1 ξ)) at h
    rw [gramGroupOperator_one] at h
    exact h
  have hShift : Tendsto (fun g : G => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    have hProduct := (continuous_const : Continuous (fun _ : G => (g₀⁻¹ : G))).mul
      (continuous_id : Continuous (id : G → G))
    have hFun : ((fun _ : G => (g₀⁻¹ : G)) * (id : G → G)) =
        fun g : G => g₀⁻¹ * g := by
      funext g
      rw [Pi.mul_apply]
      rfl
    rw [hFun] at hProduct
    simpa only [inv_mul_cancel] using hProduct.tendsto g₀
  have hOrbit := ((gramGroupOperator μ α p H ρ g₀).continuous.tendsto ξ).comp (hAtOne.comp hShift)
  have hFun : (fun g : G => gramGroupOperator μ α p H ρ g₀
      (gramGroupOperator μ α p H ρ (g₀⁻¹ * g) ξ)) =
      fun g : G => gramGroupOperator μ α p H ρ g ξ := by
    funext g
    have hProduct : gramGroupOperator μ α p H ρ g₀ *
        gramGroupOperator μ α p H ρ (g₀⁻¹ * g) = gramGroupOperator μ α p H ρ g := by
      rw [← gramGroupOperator_mul, mul_inv_cancel_left]
    exact congrArg (fun T : ρ.essentialSpace →L[ℂ] ρ.essentialSpace => T ξ) hProduct
  simp only [Function.comp_def] at hOrbit
  rw [hFun] at hOrbit
  exact hOrbit

/-- The computed original-source group operators as an actual strongly continuous unitary representation. -/
def gramStronglyContinuousUnitaryRepresentation (hp : p ∈ admissibleCStarSeminorms μ α) :
    StronglyContinuousUnitaryRepresentation G ρ.essentialSpace where
  toMonoidHom := gramGroupUnitaryRepresentation μ α p H ρ
  continuous_orbit := gramGroupOperator_continuous μ α p H ρ hp

/-- The actual strongly continuous group representation retains its original computed operator. -/
@[simp]
theorem gramStronglyContinuousUnitaryRepresentation_apply_coe
    (hp : p ∈ admissibleCStarSeminorms μ α) (g : G) :
    (gramStronglyContinuousUnitaryRepresentation μ α p H ρ hp g :
        ρ.essentialSpace →L[ℂ] ρ.essentialSpace) = gramGroupOperator μ α p H ρ g := rfl

/-- The actual strongly continuous covariant model on the computed essential Hilbert space. -/
def gramCovariantRepresentation (hp : p ∈ admissibleCStarSeminorms μ α) :
    CovariantRepresentation α ρ.essentialSpace where
  algebra := gramCoefficientRepresentation μ α p H ρ
  group := gramStronglyContinuousUnitaryRepresentation μ α p H ρ hp
  covariance := gramRepresentation_covariance μ α p H ρ

/-- The constructed covariant coefficient map is the original computed coefficient representation. -/
@[simp]
theorem gramCovariantRepresentation_algebra (hp : p ∈ admissibleCStarSeminorms μ α) :
    (gramCovariantRepresentation μ α p H ρ hp).algebra =
      gramCoefficientRepresentation μ α p H ρ := rfl

/-- The constructed covariant group map is the actual strongly continuous original-source group. -/
@[simp]
theorem gramCovariantRepresentation_group (hp : p ∈ admissibleCStarSeminorms μ α) :
    (gramCovariantRepresentation μ α p H ρ hp).group =
      gramStronglyContinuousUnitaryRepresentation μ α p H ρ hp := rfl

end

end HaarTwistedCore
