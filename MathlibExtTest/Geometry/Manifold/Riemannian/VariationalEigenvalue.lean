/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.Geometry.Manifold.Riemannian.VariationalEigenvalue
/-!
Test pins for variational Laplace eigenvalues on manifolds.
-/
open Bundle MeasureTheory
open scoped ENNReal NNReal Manifold ContDiff
noncomputable section
namespace Manifold
namespace VariationalEigenvalueTest
-- Pins unfolding of `dirichletEnergy`.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [MeasurableSpace M]
    (μ : Measure M) (u : M → ℝ) :
    dirichletEnergy I μ u = ∫⁻ x, ‖mvfderiv I u x‖ₑ ^ 2 ∂μ := rfl
-- Pins unfolding of `rayleighQuotient`.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [MeasurableSpace M]
    (μ : Measure M) (u : M → ℝ) :
    rayleighQuotient I μ u = dirichletEnergy I μ u / ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ := rfl
-- Pins unfolding of `variationalEigenvalue`.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [MeasurableSpace M]
    (W : Submodule ℝ C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) (μ : Measure M) (k : ℕ) :
    variationalEigenvalue I W μ k =
      ⨅ V : Submodule ℝ C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯, ⨅ (_ : V ≤ W),
        ⨅ (_ : Module.finrank ℝ ↥V = k + 1),
          ⨅ (_ : ∀ u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯, u ∈ V → u ≠ 0 →
            0 < ∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂μ ∧ ∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂μ < ⊤),
            ⨆ (u : ↥V), ⨆ (_ : u ≠ 0),
              rayleighQuotient I μ ⇑(u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) := rfl
-- Pins unfolding of `dirichletEigenvalue`.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [MeasurableSpace M] [BorelSpace M]
    (U : TopologicalSpace.Opens M) (k : ℕ) :
    dirichletEigenvalue I U k =
      variationalEigenvalue I (smoothTestSubmodule I U) (riemannianVolume I M) k := rfl
-- Pins unfolding of `neumannEigenvalue`.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [MeasurableSpace M] [BorelSpace M] (k : ℕ) :
    neumannEigenvalue I M k = variationalEigenvalue I ⊤ (riemannianVolume I M) k := rfl
-- Pins membership in `smoothTestSubmodule`.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (U : TopologicalSpace.Opens M) (u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) :
    (u ∈ smoothTestSubmodule I U) ↔
      (HasCompactSupport (⇑u : M → ℝ) ∧ tsupport (⇑u : M → ℝ) ⊆ (↑U : Set M)) := Iff.rfl
-- Empty family for `⊥` on `ℝ` is `⊤`.
example (k : ℕ) (μ : Measure ℝ) :
    variationalEigenvalue 𝓘(ℝ, ℝ) ⊥ μ k = ⊤ := variationalEigenvalue_bot _ _ _
-- Zero measure gives `⊤` for `W = ⊤` on `ℝ`.
example (k : ℕ) :
    variationalEigenvalue 𝓘(ℝ, ℝ) ⊤ (0 : Measure ℝ) k = ⊤ :=
      variationalEigenvalue_zero_measure _ _ _
/-- Standard bundle metric on `ℝ`, reused to build the scaled metric. -/
def stdM : Bundle.RiemannianMetric (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) :=
  (inferInstance : Bundle.RiemannianBundle (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x)).1
/-- Scaled metric on `ℝ`: `c ^ 2` times the standard inner product. -/
def scaledMetric (c : ℝ) (hc : 0 < c) :
    Bundle.RiemannianMetric (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) where
  inner := fun b => (c ^ 2) • (stdM.inner b)
  symm := fun b v w => by
    have hstd : (((stdM.inner b) v) w) = (((stdM.inner b) w) v) := stdM.symm b v w
    have h1 : ((((c ^ 2) • (stdM.inner b)) v) w) = (c ^ 2) * ((((stdM.inner b)) v) w) := by
      simp [smul_eq_mul]
    have h2 : ((((c ^ 2) • (stdM.inner b)) w) v) = (c ^ 2) * ((((stdM.inner b)) w) v) := by
      simp [smul_eq_mul]
    have h3 : (c ^ 2) * ((((stdM.inner b)) v) w) = (c ^ 2) * ((((stdM.inner b)) w) v) := by
      rw [hstd]
    exact h1.trans (h3.trans h2.symm)
  pos := fun b v hv => by
    have hc2 : (0 : ℝ) < c ^ 2 := pow_pos hc 2
    have hQ : (0 : ℝ) < ((((stdM.inner b)) v) v) := stdM.pos b v hv
    have h1 : ((((c ^ 2) • (stdM.inner b)) v) v) = (c ^ 2) * ((((stdM.inner b)) v) v) := by
      simp [smul_eq_mul]
    rw [h1]
    exact mul_pos hc2 hQ
  continuousAt := fun b => by
    have hstdC : ContinuousAt (fun v : TangentSpace 𝓘(ℝ, ℝ) b => ((((stdM.inner b)) v) v)) 0 :=
      stdM.continuousAt b
    have heq : (fun v : TangentSpace 𝓘(ℝ, ℝ) b => ((((c ^ 2) • (stdM.inner b)) v) v)) =
        (fun v => (c ^ 2) * ((((stdM.inner b)) v) v)) := by
      funext v
      simp [smul_eq_mul]
    rw [heq]
    exact continuousAt_const.mul hstdC
  isVonNBounded := fun b => by
    have heq : {v : TangentSpace 𝓘(ℝ, ℝ) b | ((((c ^ 2) • (stdM.inner b)) v) v) < 1} =
        {v | (c ^ 2) * ((((stdM.inner b)) v) v) < 1} := by
      ext v
      simp [smul_eq_mul]
    have hsub : {v : TangentSpace 𝓘(ℝ, ℝ) b | (c ^ 2) * ((((stdM.inner b)) v) v) < 1} ⊆
        Metric.ball (0 : TangentSpace 𝓘(ℝ, ℝ) b) (c⁻¹ + 1) := by
      intro v hv
      have hQnn : (0 : ℝ) ≤ ((((stdM.inner b)) v) v) := by
        rcases eq_or_ne v 0 with rfl | hz
        · have h0 : ((((stdM.inner b)) 0) 0) = 0 := by simp
          exact le_of_eq h0.symm
        · exact le_of_lt (stdM.pos b v hz)
      have hnormStd : ‖v‖ = Real.sqrt ((((stdM.inner b)) v) v) := rfl
      have hQlt : (c ^ 2) * ((((stdM.inner b)) v) v) < 1 := hv
      have hnorm2 : ‖v‖ ^ 2 = ((((stdM.inner b)) v) v) := by
        rw [hnormStd, Real.sq_sqrt hQnn]
      have hmul : (c ^ 2) * (‖v‖ ^ 2) < 1 := by
        rw [hnorm2]
        exact hQlt
      have hsq_eq : (c * ‖v‖) ^ 2 = (c ^ 2) * (‖v‖ ^ 2) := by ring
      have hsq_lt : (c * ‖v‖) ^ 2 < 1 := by
        rw [hsq_eq]
        exact hmul
      have hcx_lt : c * ‖v‖ < 1 := by nlinarith [hsq_lt, sq_nonneg (c * ‖v‖ - 1)]
      have hlt_inv : ‖v‖ < c⁻¹ := by
        by_contra hcon
        push Not at hcon
        have hle2 : c * c⁻¹ ≤ c * ‖v‖ :=
          mul_le_mul_of_nonneg_left hcon (le_of_lt hc)
        have hcc2 : c * c⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hc)
        rw [hcc2] at hle2
        linarith
      have hle : ‖v‖ < c⁻¹ + 1 := by linarith
      have hmem : v ∈ Metric.ball (0 : TangentSpace 𝓘(ℝ, ℝ) b) (c⁻¹ + 1) := by
        rw [Metric.mem_ball, dist_zero_right]
        exact hle
      exact hmem
    have hbounded : Bornology.IsBounded (Metric.ball (0 : TangentSpace 𝓘(ℝ, ℝ) b) (c⁻¹ + 1)) :=
      Metric.isBounded_ball
    have hball : Bornology.IsVonNBounded ℝ (Metric.ball (0 : TangentSpace 𝓘(ℝ, ℝ) b) (c⁻¹ + 1)) :=
      NormedSpace.isVonNBounded_of_isBounded ℝ hbounded
    rw [heq]
    exact hball.subset hsub
-- Standard inner on `ℝ` is the product of the trivialisation coordinates.
theorem std_inner_eq_phi (x : ℝ) (v : TangentSpace 𝓘(ℝ, ℝ) x) :
    ((((stdM.inner x) v) v)) =
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v) *
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v) := by
  have h1 : inner ℝ v v = ((((stdM.inner x) v) v)) := rfl
  have h2 : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
  have h3 : ‖v‖ = ‖((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)‖ :=
    norm_tangentSpace_vectorSpace
  have h4 : ‖v‖ ^ 2 = ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v) *
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v) := by
    rw [h3, Real.norm_eq_abs, sq_abs, pow_two]
  have h5 : ((((stdM.inner x) v) v)) = ‖v‖ ^ 2 := h1.symm.trans h2
  rw [h5]
  exact h4
-- The differential norm uses the bundle metric, giving `c⁻¹`.
theorem scaled_norm (c : ℝ) (hc : 0 < c) (x : ℝ) :
    letI : RiemannianBundle (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) := ⟨scaledMetric c hc⟩;
    ‖mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x‖ = c⁻¹ := by
  let : RiemannianBundle (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) := ⟨scaledMetric c hc⟩
  show ‖mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x‖ = c⁻¹
  have hmv : mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x = fderiv ℝ (fun x => x) x ∘SL
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap := mvfderiv_eq_fderiv
  have hfd : fderiv ℝ (fun x => x) x = ContinuousLinearMap.id ℝ ℝ := by simp
  have hTeq : mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap := by
    rw [hmv, hfd, ContinuousLinearMap.id_comp]
  have hT : ∀ v : TangentSpace 𝓘(ℝ, ℝ) x, (mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x) v =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v := fun v => by
    rw [hTeq]
    rfl
  have hinner : ∀ v : TangentSpace 𝓘(ℝ, ℝ) x, ((((c ^ 2) • (stdM.inner x)) v) v) =
      (c ^ 2) * ((((stdM.inner x)) v) v) := fun v => by
    simp [smul_eq_mul]
  have hnorm0a : ∀ v : TangentSpace 𝓘(ℝ, ℝ) x,
      ‖v‖ = Real.sqrt (((((c ^ 2) • (stdM.inner x)) v) v)) := fun v => rfl
  have hnorm0 : ∀ v : TangentSpace 𝓘(ℝ, ℝ) x, ‖v‖ = Real.sqrt
      (c ^ 2 * ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v) *
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)) := fun v => by
    rw [hnorm0a v, hinner v, std_inner_eq_phi x v]
    congr 1
    ring
  have hreal : ∀ v : TangentSpace 𝓘(ℝ, ℝ) x, Real.sqrt
      (c ^ 2 * ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v) *
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)) =
        c * ‖((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)‖ := fun v => by
    have hsq : c ^ 2 * ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v) *
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v) =
        (c * ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)) ^ 2 := by ring
    have hsqrt : Real.sqrt ((c * ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)) ^ 2) =
        |c * ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)| := Real.sqrt_sq_eq_abs _
    have habs : |c * ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)| =
        c * |((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)| := by
      rw [abs_mul, abs_of_pos hc]
    have hnormabs : |((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)| =
        ‖((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)‖ := (Real.norm_eq_abs _).symm
    rw [hsq, hsqrt, habs, hnormabs]
  have hnorm : ∀ v : TangentSpace 𝓘(ℝ, ℝ) x,
      ‖v‖ = c * ‖((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)‖ := fun v => by
    rw [hnorm0 v]
    exact hreal v
  have hle : ∀ v : TangentSpace 𝓘(ℝ, ℝ) x,
      ‖(mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x) v‖ ≤ c⁻¹ * ‖v‖ := fun v => by
    have hTv : ‖(mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x) v‖ =
        ‖((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)‖ := by
      rw [hT v]
    have hnv : ‖v‖ = c * ‖((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)‖ := hnorm v
    have heq2 : c⁻¹ * (c * ‖((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)‖) =
        ‖((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v)‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]
    rw [hTv, hnv]
    exact le_of_eq heq2.symm
  have hupper : ‖mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x‖ ≤ c⁻¹ :=
    ContinuousLinearMap.opNorm_le_bound _ (le_of_lt (inv_pos.mpr hc)) hle
  have hphi : ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1)) = 1 := by simp
  have hnormv0 : ‖((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1)‖ = c := by
    have h1 : ‖((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1)‖ =
        c * ‖((NormedSpace.fromTangentSpace (𝕜 := ℝ) x)
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1))‖ :=
      hnorm _
    have h2 : ‖((NormedSpace.fromTangentSpace (𝕜 := ℝ) x)
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1))‖ = 1 := by
      rw [hphi, norm_one]
    rw [h1, h2, mul_one]
  have hTv0 : ‖(mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1)‖ = 1 := by
    rw [hT _, hphi, norm_one]
  have hle0 : ‖(mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1)‖ ≤
      ‖mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x‖ *
        ‖((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1)‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have hlow : c⁻¹ ≤ ‖mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x‖ := by
    have h1le : (1 : ℝ) ≤ ‖mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x‖ * c := by
      rw [← hTv0, ← hnormv0]
      exact hle0
    have hmul : c⁻¹ * c ≤ ‖mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x‖ * c := by
      rw [inv_mul_cancel₀ (ne_of_gt hc)]
      exact h1le
    exact le_of_mul_le_mul_right hmul hc
  exact le_antisymm hupper hlow
-- Standard metric gives norm `1`, unlike the scaled `1 / 2`.
example (x : ℝ) : ‖mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x‖ = 1 := by
  have hmv : mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x = fderiv ℝ (fun x => x) x ∘SL
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap := mvfderiv_eq_fderiv
  have hfd : fderiv ℝ (fun x => x) x = ContinuousLinearMap.id ℝ ℝ := by simp
  have hTeq : mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap := by
    rw [hmv, hfd, ContinuousLinearMap.id_comp]
  have hT : ∀ v : TangentSpace 𝓘(ℝ, ℝ) x, (mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x) v =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v := fun v => by
    rw [hTeq]
    rfl
  have hnormStd : ∀ v : TangentSpace 𝓘(ℝ, ℝ) x,
      ‖v‖ = ‖(NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v‖ := fun v =>
    norm_tangentSpace_vectorSpace
  have hle : ∀ v : TangentSpace 𝓘(ℝ, ℝ) x,
      ‖(mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x) v‖ ≤ 1 * ‖v‖ := fun v => by
    have hTv : ‖(mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x) v‖ =
        ‖(NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v‖ := by
      rw [hT v]
    rw [hTv, hnormStd v, one_mul]
  have hupper : ‖mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one hle
  have hev : ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1)) = 1 := by simp
  have hnormv0 : ‖((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1)‖ = 1 := by
    rw [hnormStd _, hev, norm_one]
  have hTv0 : ‖(mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1)‖ = 1 := by
    rw [hT _, hev, norm_one]
  have hle0 : ‖(mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1)‖ ≤
      ‖mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x‖ *
        ‖((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm 1)‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [hTv0, hnormv0, mul_one] at hle0
  exact le_antisymm hupper hle0
-- For `c = 2` the scaled norm is `1 / 2`.
example (x : ℝ) :
    letI : RiemannianBundle (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨scaledMetric 2 (by norm_num)⟩;
    ‖mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x‖ = 1 / 2 := by
  let : RiemannianBundle (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) := ⟨scaledMetric 2 (by norm_num)⟩
  show ‖mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x‖ = 1 / 2
  have hc2 : (0 : ℝ) < 2 := by norm_num
  have hscaled : ‖mvfderiv 𝓘(ℝ, ℝ) (fun x => x) x‖ = (2 : ℝ)⁻¹ := scaled_norm 2 hc2 x
  rw [hscaled, one_div]
-- `1 / 2 ≠ 1` records the metric dependence.
example : (1 / 2 : ℝ) ≠ 1 := by norm_num
-- Per-metric Neumann is bounded by Dirichlet.
theorem per_metric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T3Space M] [MeasurableSpace M] [BorelSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (U : TopologicalSpace.Opens M) (k : ℕ) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      Bundle.instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric;
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M;
    neumannEigenvalue I M k ≤ dirichletEigenvalue I U k := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    Bundle.instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  show neumannEigenvalue I M k ≤ dirichletEigenvalue I U k
  have hle : smoothTestSubmodule I U ≤ (⊤ : Submodule ℝ C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) := le_top
  have hanti : variationalEigenvalue I ⊤ (riemannianVolume I M) k ≤
      variationalEigenvalue I (smoothTestSubmodule I U) (riemannianVolume I M) k :=
    variationalEigenvalue_antitone I hle (riemannianVolume I M) k
  exact hanti
end VariationalEigenvalueTest
end Manifold
