/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Riemannian.MetricCkTopology
import MathlibExt.Geometry.Manifold.RiemannianMetricExistence
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Tests for the C^k topology on smooth Riemannian metrics

This file tests `Manifold.metricInCoordinates` and `Manifold.metricCkTopology`.
It contains a populated closed-manifold example on `S^2` and a near-miss on `R`
separating the `C^0` and `C^1` topologies. The near-miss matters because a pointwise
or `C^0` proxy would make the `C^0` and `C^1` statements agree: the wobble metrics
converge uniformly on compacts at order zero, while their order-one derivatives stay
at distance one from the flat limit at a single point.
-/

open Bundle Filter Topology
open scoped ContDiff Manifold

namespace MetricCkTopologyTests

/-- The 2-sphere as a subtype of `EuclideanSpace R (Fin 3)`. -/
abbrev S2 : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1)

/-- Instance check: the sphere is compact. -/
example : CompactSpace S2 := inferInstance

/-- Instance check: the sphere is boundaryless over `R 2`. -/
example : BoundarylessManifold (𝓡 2) S2 := inferInstance

/-- Abbreviation for smooth metrics on `S2`. -/
abbrev MetS2 :=
  Bundle.ContMDiffRiemannianMetric (𝓡 2) ∞ (EuclideanSpace ℝ (Fin 2))
    (fun x : S2 ↦ TangentSpace (𝓡 2) x)

/-- A smooth background metric on `S2` from existence. -/
noncomputable def sphereMetric0 : MetS2 :=
  Classical.choice
    (MathlibExt.Geometry.Manifold.RiemannianMetricExistenceWanted.riemannianMetricExistence
      (I := 𝓡 2) (M := S2))

/-- Constant conformal factor tending to one. -/
noncomputable def sphereScale (n : ℕ) : ℝ := 1 + 1 / ((n : ℝ) + 1)

/-- Positivity of the constant factor. -/
theorem sphereScale_pos (n : ℕ) : 0 < sphereScale n := by
  unfold sphereScale
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hn
  linarith

/-- The constant factor is never one. -/
theorem sphereScale_ne_one (n : ℕ) : sphereScale n ≠ 1 := by
  unfold sphereScale
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  have hne : (1 : ℝ) / ((n : ℝ) + 1) ≠ 0 := one_div_ne_zero (ne_of_gt hpos)
  intro h
  have hzero : (1 : ℝ) / ((n : ℝ) + 1) = 0 := by linarith
  exact hne hzero

/-- The rescaled sequence on `S2`. -/
noncomputable def sphereSeq (n : ℕ) : MetS2 :=
  sphereMetric0.conformalScale (fun _ ↦ sphereScale n) contMDiff_const
    (fun _ ↦ sphereScale_pos n)

/-- An explicit point of `S2`. -/
noncomputable def spherePoint : S2 :=
  ⟨EuclideanSpace.single (0 : Fin (2 + 1)) (1 : ℝ), by
    rw [Metric.mem_sphere]
    simp [dist_zero_right]⟩

/-- An explicit nonzero tangent vector at `spherePoint`. -/
noncomputable def sphereVec : TangentSpace (𝓡 2) spherePoint :=
  EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

/-- The explicit tangent vector is nonzero. -/
theorem sphereVec_ne : sphereVec ≠ 0 := by
  have h : (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) :
      EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    simp
  exact h

/-- Each rescaled metric differs from the background metric. -/
theorem sphereSeq_ne (n : ℕ) : sphereSeq n ≠ sphereMetric0 := by
  intro h
  have hq : 0 < sphereMetric0.inner spherePoint sphereVec sphereVec := by
    cases sphereMetric0 with
    | mk inner hsymm hpos hbound hcont =>
      exact hpos spherePoint sphereVec sphereVec_ne
  have harg := congrArg
    (fun g : MetS2 ↦ g.inner spherePoint sphereVec sphereVec) h
  simp only [sphereSeq] at harg
  rw [Bundle.ContMDiffRiemannianMetric.conformalScale_inner_apply] at harg
  have hqne : sphereMetric0.inner spherePoint sphereVec sphereVec ≠ 0 := ne_of_gt hq
  have hEq : sphereScale n * sphereMetric0.inner spherePoint sphereVec sphereVec =
      1 * sphereMetric0.inner spherePoint sphereVec sphereVec := by
    rw [one_mul]
    exact harg
  have hScale1 : sphereScale n = 1 := mul_right_cancel₀ hqne hEq
  exact sphereScale_ne_one n hScale1

/-- The constant factors tend to one. -/
theorem sphereScale_tendsto : Tendsto sphereScale atTop (𝓝 1) := by
  unfold sphereScale
  have h0 : Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto (fun n : ℕ ↦ (1 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 ((1 : ℝ) + 0)) :=
    tendsto_const_nhds.add h0
  have hEq : ((1 : ℝ) + 0) = 1 := add_zero 1
  rw [hEq] at h1
  exact h1

/-- The rescaled metrics converge in every `C^k` topology. -/
theorem sphere_tendsto (k : ℕ∞) :
    Tendsto sphereSeq atTop (@nhds _ (Manifold.metricCkTopology (𝓡 2) S2 k) sphereMetric0) := by
  unfold sphereSeq
  exact Manifold.tendsto_conformalScale_const_metricCkTopology (I := 𝓡 2) (M := S2)
    sphereMetric0 (fun n ↦ sphereScale n) (fun _ ↦ sphereScale_pos _) sphereScale_tendsto k

/-- Populated closed-manifold convergence with distinct terms. -/
theorem closed_manifold_populated :
    ∃ g₀ : MetS2, ∃ g : ℕ → MetS2, (∀ n, g n ≠ g₀) ∧
      ∀ k : ℕ∞, Tendsto g atTop (@nhds _ (Manifold.metricCkTopology (𝓡 2) S2 k) g₀) :=
  ⟨sphereMetric0, sphereSeq, sphereSeq_ne, sphere_tendsto⟩

/-- Smooth metrics on `R` with the `I(R,R)` model. -/
abbrev MetR :=
  Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, ℝ) ∞ ℝ
    (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x)

/-- The flat metric on `R`, lowered from `omega` to `infty`. -/
noncomputable def flatMetric : MetR :=
  (riemannianMetricVectorSpace ℝ).ofLE le_top

/-- The wobble factor. -/
noncomputable def wobble (n : ℕ) (x : ℝ) : ℝ :=
  1 + (1 + Real.sin (((n : ℝ) + 1) * x)) / ((n : ℝ) + 1)

/-- Positivity of the wobble factor. -/
theorem wobble_pos (n : ℕ) (x : ℝ) : 0 < wobble n x := by
  unfold wobble
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  have hlow : (-1 : ℝ) ≤ Real.sin (((n : ℝ) + 1) * x) := Real.neg_one_le_sin _
  have hnn : (0 : ℝ) ≤ (1 + Real.sin (((n : ℝ) + 1) * x)) / ((n : ℝ) + 1) := by
    apply div_nonneg _ hn.le
    linarith
  linarith

/-- Smoothness of the wobble factor. -/
theorem wobble_smooth (n : ℕ) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ) ∞ (wobble n) := by
  have hDiff : ContDiff ℝ ∞ (wobble n) := by
    unfold wobble
    fun_prop
  exact hDiff.contMDiff

/-- The wobble metrics. -/
noncomputable def wobbleMetric (n : ℕ) : MetR :=
  flatMetric.conformalScale (wobble n) (wobble_smooth n) (wobble_pos n)

/-- The identity chart belongs to the maximal atlas of `R`. -/
theorem refl_mem_maximalAtlas :
    OpenPartialHomeomorph.refl ℝ ∈
      IsManifold.maximalAtlas 𝓘(ℝ, ℝ) ∞ ℝ :=
  IsManifold.subset_maximalAtlas (chartedSpaceSelf_atlas.mpr rfl)

/-- The identity chart target is everything. -/
theorem refl_target :
    ((OpenPartialHomeomorph.refl ℝ).extend 𝓘(ℝ, ℝ)).target = Set.univ := by
  rw [OpenPartialHomeomorph.extend_target]
  ext x
  refine ⟨fun _ => Set.mem_univ x, fun _ => ?_⟩
  rw [Set.mem_inter_iff, Set.mem_preimage]
  exact ⟨Set.mem_univ _, ⟨x, rfl⟩⟩

/-- The inverse extended identity chart is the identity. -/
theorem refl_symm_apply (x : ℝ) :
    ((OpenPartialHomeomorph.refl ℝ).extend 𝓘(ℝ, ℝ)).symm x = x := by
  rw [OpenPartialHomeomorph.extend_coe_symm]
  rfl

/-- The derivative of the inverse identity chart, viewed as a map on `R`. -/
theorem refl_D_eq (x : ℝ) :
    (show ℝ →L[ℝ] ℝ from mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        ((OpenPartialHomeomorph.refl ℝ).extend 𝓘(ℝ, ℝ)).symm
        ((OpenPartialHomeomorph.refl ℝ).extend 𝓘(ℝ, ℝ)).target x) =
      ContinuousLinearMap.id ℝ ℝ := by
  have hsymm : ⇑((OpenPartialHomeomorph.refl ℝ).extend 𝓘(ℝ, ℝ)).symm = id :=
    funext refl_symm_apply
  rw [hsymm, refl_target]
  exact mfderivWithin_id (uniqueMDiffWithinAt_univ 𝓘(ℝ, ℝ))

/-- The flat coordinate expression at `1, 1` equals one. -/
theorem flat_coord (x : ℝ) :
    Manifold.metricInCoordinates flatMetric (OpenPartialHomeomorph.refl ℝ) x 1 1 = 1 := by
  unfold Manifold.metricInCoordinates
  rw [refl_D_eq x, refl_symm_apply x]
  simp [flatMetric, riemannianMetricVectorSpace]
  show ((innerSL ℝ) (1 : ℝ)) (1 : ℝ) = 1
  simp [innerSL_apply_apply]

/-- Value pin at order zero. -/
theorem pin_coord (n : ℕ) (x : ℝ) :
    Manifold.metricInCoordinates (wobbleMetric n) (OpenPartialHomeomorph.refl ℝ) x 1 1 =
      wobble n x := by
  unfold wobbleMetric
  rw [Manifold.metricInCoordinates_conformalScale, refl_symm_apply x]
  simp only [smul_apply, smul_eq_mul, flat_coord x, mul_one]

/-- The flat order-one derivative vanishes. -/
theorem flat_deriv_zero :
    (((iteratedFDerivWithin ℝ 1
        (Manifold.metricInCoordinates flatMetric (OpenPartialHomeomorph.refl ℝ))
        ((OpenPartialHomeomorph.refl ℝ).extend 𝓘(ℝ, ℝ)).target 0)
      (fun _ ↦ (1 : ℝ))) (1 : ℝ)) (1 : ℝ) = 0 := by
  have htarget : ((OpenPartialHomeomorph.refl ℝ).extend 𝓘(ℝ, ℝ)).target = Set.univ :=
    refl_target
  have hconst : Manifold.metricInCoordinates flatMetric (OpenPartialHomeomorph.refl ℝ) =
      fun _ ↦ Manifold.metricInCoordinates flatMetric (OpenPartialHomeomorph.refl ℝ) 0 := by
    funext y
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    unfold Manifold.metricInCoordinates
    rw [refl_D_eq y, refl_D_eq 0, refl_symm_apply y, refl_symm_apply 0]
    simp [flatMetric, riemannianMetricVectorSpace]
  rw [htarget, hconst, iteratedFDerivWithin_univ, iteratedFDeriv_one_apply]
  simp

set_option maxSynthPendingDepth 2 in
-- Instances on the iterated-derivative codomain are not found at the default depth 1;
-- the differentiability query on `F` below fails to synthesize without it.
/-- Order-one derivative pin blocking `C^1` convergence. -/
theorem pin_deriv_one (n : ℕ) :
    (((iteratedFDerivWithin ℝ 1
        (Manifold.metricInCoordinates (wobbleMetric n) (OpenPartialHomeomorph.refl ℝ))
        ((OpenPartialHomeomorph.refl ℝ).extend 𝓘(ℝ, ℝ)).target 0)
      (fun _ ↦ (1 : ℝ))) (1 : ℝ)) (1 : ℝ) = 1 := by
  have htarget : ((OpenPartialHomeomorph.refl ℝ).extend 𝓘(ℝ, ℝ)).target = Set.univ :=
    refl_target
  rw [htarget, iteratedFDerivWithin_univ, iteratedFDeriv_one_apply]
  set F := Manifold.metricInCoordinates (wobbleMetric n) (OpenPartialHomeomorph.refl ℝ)
    with hF
  have hFeq : (fun x ↦ F x 1 1) = wobble n := funext (fun x ↦ pin_coord n x)
  have hCont : ContDiffOn ℝ ∞ F Set.univ := by
    have he := refl_mem_maximalAtlas
    have h := Manifold.contDiffOn_metricInCoordinates (I := 𝓘(ℝ, ℝ)) (M := ℝ)
      (wobbleMetric n) (e := OpenPartialHomeomorph.refl ℝ) he
    rwa [htarget] at h
  have hAt : ContDiffAt ℝ ∞ F 0 := hCont.contDiffAt Filter.univ_mem
  have hDiff : DifferentiableAt ℝ F 0 := hAt.differentiableAt (by simp)
  have hHas : HasFDerivAt F (fderiv ℝ F 0) 0 := hDiff.hasFDerivAt
  let ev1 : (ℝ →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)
  let ev2 : (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] (ℝ →L[ℝ] ℝ) :=
    ContinuousLinearMap.apply ℝ (ℝ →L[ℝ] ℝ) (1 : ℝ)
  let ev : (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ := ev1.comp ev2
  have hev : ∀ L : (ℝ →L[ℝ] ℝ →L[ℝ] ℝ), ev L = (L 1) 1 := fun L => rfl
  have hcomp : HasFDerivAt (fun x ↦ ev (F x)) (ev.comp (fderiv ℝ F 0)) 0 :=
    (ContinuousLinearMap.hasFDerivAt ev).comp 0 hHas
  have hw : HasDerivAt (wobble n) 1 (0 : ℝ) := by
    have hc : ((n : ℝ) + 1) ≠ 0 := by
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by
        have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
    have hlin : HasDerivAt (fun x : ℝ ↦ ((n : ℝ) + 1) * x) ((n : ℝ) + 1) (0 : ℝ) := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul ((n : ℝ) + 1)
    have hsin : HasDerivAt (fun x : ℝ ↦ Real.sin (((n : ℝ) + 1) * x))
        (Real.cos (((n : ℝ) + 1) * 0) * ((n : ℝ) + 1)) (0 : ℝ) :=
      hlin.sin
    have hadd : HasDerivAt (fun x : ℝ ↦ 1 + Real.sin (((n : ℝ) + 1) * x))
        (Real.cos (((n : ℝ) + 1) * 0) * ((n : ℝ) + 1)) (0 : ℝ) :=
      hsin.const_add 1
    have hdiv : HasDerivAt
        (fun x : ℝ ↦ (1 + Real.sin (((n : ℝ) + 1) * x)) / ((n : ℝ) + 1))
        (Real.cos (((n : ℝ) + 1) * 0) * ((n : ℝ) + 1) / ((n : ℝ) + 1)) (0 : ℝ) :=
      hadd.div_const _
    have hfin : HasDerivAt (wobble n)
        (Real.cos (((n : ℝ) + 1) * 0) * ((n : ℝ) + 1) / ((n : ℝ) + 1)) (0 : ℝ) := by
      unfold wobble
      exact hdiv.const_add 1
    have hthis : Real.cos (((n : ℝ) + 1) * 0) * ((n : ℝ) + 1) / ((n : ℝ) + 1) = 1 := by
      simp [Real.cos_zero, hc]
    rwa [hthis] at hfin
  have hFeq2 : (fun x ↦ ev (F x)) = wobble n := by
    funext x
    rw [hev]
    exact congrFun hFeq x
  have hfd : fderiv ℝ (fun x ↦ ev (F x)) 0 = ev.comp (fderiv ℝ F 0) :=
    hcomp.fderiv
  rw [hFeq2] at hfd
  have hwF : fderiv ℝ (wobble n) 0 = ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) :=
    hw.hasFDerivAt.fderiv
  have heq : ev.comp (fderiv ℝ F 0) = ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) :=
    hfd.symm.trans hwF
  have hval : ev (fderiv ℝ F 0 1) = 1 := by
    have hcongr := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) heq
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_one] at hcongr
    exact hcongr
  simpa [hev] using hval

/-- Wrong-coefficient mutation refuted. -/
theorem pin_mutation :
    Manifold.metricInCoordinates (wobbleMetric 0) (OpenPartialHomeomorph.refl ℝ) 0 1 1 ≠ 1 := by
  rw [pin_coord]
  have h2 : wobble 0 0 = 2 := by
    unfold wobble
    simp [Real.sin_zero]
    norm_num
  rw [h2]
  norm_num

set_option synthInstance.maxHeartbeats 100000 in
-- Instance synthesis for `ℝ →L[ℝ] ℝ →L[ℝ] ℝ` times out at the default 20000 heartbeats.
set_option maxSynthPendingDepth 2 in
-- Instances on the iterated-derivative codomain are not found at the default depth 1;
-- the `rewrite` steps in the norm estimate on compact sets below fail without it.
/-- `C^0` convergence of the wobble metrics. -/
theorem wobble_tendsto_C0 :
    Tendsto wobbleMetric atTop
      (@nhds _ (Manifold.metricCkTopology 𝓘(ℝ, ℝ) ℝ 0) flatMetric) := by
  rw [Manifold.tendsto_metricCkTopology_iff]
  intro e he i hi K hK hKs
  have hi0 : i = 0 := by
    have h0 : (i : ℕ∞) ≤ ((0 : ℕ) : ℕ∞) := by simpa using hi
    have hle := WithTop.coe_le_coe.mp h0
    omega
  subst hi0
  set s := (e.extend 𝓘(ℝ, ℝ)).target with hs
  have hU : UniqueDiffOn ℝ s := by
    rw [hs, OpenPartialHomeomorph.extend_target]
    exact ModelWithCorners.uniqueDiffOn_preimage _ e.open_target
  have hflatD : ContDiffOn ℝ ∞ (Manifold.metricInCoordinates flatMetric e) s :=
    Manifold.contDiffOn_metricInCoordinates flatMetric he
  have hcont : ContinuousOn
      (iteratedFDerivWithin ℝ 0 (Manifold.metricInCoordinates flatMetric e) s) s :=
    hflatD.continuousOn_iteratedFDerivWithin (by simp) hU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKs)
  set C' : ℝ := |C| + 1 with hC'
  have hCpos : 0 < C' := by positivity
  have hCle : ∀ x ∈ K, ‖iteratedFDerivWithin ℝ 0
      (Manifold.metricInCoordinates flatMetric e) s x‖ ≤ C' := by
    intro x hx
    calc ‖iteratedFDerivWithin ℝ 0
            (Manifold.metricInCoordinates flatMetric e) s x‖
        ≤ C := hC x hx
      _ ≤ |C| := le_abs_self C
      _ ≤ C' := by rw [hC']; exact le_add_of_nonneg_right zero_le_one
  have hiter_sub : ∀ (m : ℕ) (x : ℝ),
      iteratedFDerivWithin ℝ 0
        (fun y ↦ Manifold.metricInCoordinates (wobbleMetric m) e y -
          Manifold.metricInCoordinates flatMetric e y) s x =
        iteratedFDerivWithin ℝ 0
          (Manifold.metricInCoordinates (wobbleMetric m) e) s x -
        iteratedFDerivWithin ℝ 0
          (Manifold.metricInCoordinates flatMetric e) s x := by
    intro m x
    ext
    simp [iteratedFDerivWithin_zero_apply]
  have hdist : ∀ (m : ℕ) (x : ℝ),
      dist (iteratedFDerivWithin ℝ 0
        (Manifold.metricInCoordinates (wobbleMetric m) e) s x)
        (iteratedFDerivWithin ℝ 0 (Manifold.metricInCoordinates flatMetric e) s x) =
      dist (Manifold.metricInCoordinates (wobbleMetric m) e x)
        (Manifold.metricInCoordinates flatMetric e x) := by
    intro m x
    rw [dist_eq_norm, dist_eq_norm, ← hiter_sub m x, norm_iteratedFDerivWithin_zero]
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim : Tendsto (fun m : ℕ ↦ (2 * C') / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun m : ℕ ↦ (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := h0.const_mul (2 * C')
    have heq : (fun m : ℕ ↦ (2 * C') / ((m : ℝ) + 1)) =
        (fun m : ℕ ↦ (2 * C') * (1 / ((m : ℝ) + 1))) := by
      funext m
      rw [one_div, div_eq_mul_inv]
    rw [heq]
    simpa [mul_zero] using h1
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim ε hε
  refine Filter.eventually_atTop.mpr ⟨N, fun m hm x hx ↦ ?_⟩
  have hmN : (N : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
  have hnpos : (0 : ℝ) < (m : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    linarith
  have hbound : ‖Manifold.metricInCoordinates flatMetric e x‖ ≤ C' := by
    have := hCle x hx
    rwa [norm_iteratedFDerivWithin_zero] at this
  have hconf : Manifold.metricInCoordinates (wobbleMetric m) e x =
      wobble m ((e.extend 𝓘(ℝ, ℝ)).symm x) •
        Manifold.metricInCoordinates flatMetric e x := by
    have := Manifold.metricInCoordinates_conformalScale (I := 𝓘(ℝ, ℝ))
      flatMetric (wobble m) (wobble_smooth m) (wobble_pos m) e x
    simpa [wobbleMetric] using this
  have hsub : Manifold.metricInCoordinates (wobbleMetric m) e x -
      Manifold.metricInCoordinates flatMetric e x =
      ((wobble m ((e.extend 𝓘(ℝ, ℝ)).symm x) - 1) : ℝ) •
        Manifold.metricInCoordinates flatMetric e x := by
    rw [hconf, sub_smul, one_smul]
  have hsin_lo : (-1 : ℝ) ≤ Real.sin (((m : ℝ) + 1) * (e.extend 𝓘(ℝ, ℝ)).symm x) :=
    Real.neg_one_le_sin _
  have hsin_hi : Real.sin (((m : ℝ) + 1) * (e.extend 𝓘(ℝ, ℝ)).symm x) ≤ 1 :=
    Real.sin_le_one _
  have hwsub : |wobble m ((e.extend 𝓘(ℝ, ℝ)).symm x) - 1| ≤ 2 / ((m : ℝ) + 1) := by
    unfold wobble
    rw [add_sub_cancel_left]
    rw [abs_div, abs_of_pos hnpos]
    apply div_le_div_of_nonneg_right _ hnpos.le
    rw [abs_le]
    constructor <;> linarith
  have hCnn : (0 : ℝ) ≤ C' := le_of_lt hCpos
  have h2Cnn : (0 : ℝ) ≤ 2 * C' := mul_nonneg (by norm_num) hCnn
  have hdiv_nn : (0 : ℝ) ≤ (2 * C') / ((m : ℝ) + 1) :=
    div_nonneg h2Cnn (le_of_lt hnpos)
  have hNε := hN m hm
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hdiv_nn] at hNε
  rw [dist_comm, hdist, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
  have hdiv2_nn : (0 : ℝ) ≤ 2 / ((m : ℝ) + 1) :=
    div_nonneg (by norm_num) (le_of_lt hnpos)
  have hstep : |wobble m ((e.extend 𝓘(ℝ, ℝ)).symm x) - 1| *
        ‖Manifold.metricInCoordinates flatMetric e x‖ ≤
        (2 / ((m : ℝ) + 1)) * C' :=
    mul_le_mul hwsub hbound (norm_nonneg _) hdiv2_nn
  calc |wobble m ((e.extend 𝓘(ℝ, ℝ)).symm x) - 1| *
        ‖Manifold.metricInCoordinates flatMetric e x‖
      ≤ (2 / ((m : ℝ) + 1)) * C' := hstep
    _ = (2 * C') / ((m : ℝ) + 1) := by ring
    _ < ε := hNε

set_option maxSynthPendingDepth 2 in
-- Instances on the iterated-derivative codomain are not found at the default depth 1;
-- the continuous evaluation map below fails to synthesize without it.
/-- Failure of `C^1` convergence. -/
theorem wobble_not_tendsto_C1 :
    ¬ Tendsto wobbleMetric atTop
      (@nhds _ (Manifold.metricCkTopology 𝓘(ℝ, ℝ) ℝ 1) flatMetric) := by
  intro h
  rw [Manifold.tendsto_metricCkTopology_iff] at h
  have h1 := h _ refl_mem_maximalAtlas 1 le_rfl {0} isCompact_singleton (by
    rw [refl_target]
    exact Set.singleton_subset_iff.mpr (Set.mem_univ 0))
  rw [tendstoUniformlyOn_singleton_iff_tendsto] at h1
  have hcont_eval : Continuous
      (fun D : ℝ [×1]→L[ℝ] (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) =>
        ((D (fun _ : Fin 1 ↦ (1 : ℝ))) (1 : ℝ)) (1 : ℝ)) := by
    fun_prop
  have hlim := (hcont_eval.tendsto _).comp h1
  simp only [Function.comp_def, pin_deriv_one, flat_deriv_zero] at hlim
  have hconst1 : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique hconst1 hlim
  exact one_ne_zero h10

set_option maxSynthPendingDepth 2 in
-- Instances on the iterated-derivative codomain are not found at the default depth 1;
-- the continuous evaluation map below fails to synthesize without it.
/-- Failure of `C^2` convergence. -/
theorem wobble_not_tendsto_C2 :
    ¬ Tendsto wobbleMetric atTop
      (@nhds _ (Manifold.metricCkTopology 𝓘(ℝ, ℝ) ℝ 2) flatMetric) := by
  intro h
  rw [Manifold.tendsto_metricCkTopology_iff] at h
  have h1 := h _ refl_mem_maximalAtlas 1 (by decide) {0} isCompact_singleton (by
    rw [refl_target]
    exact Set.singleton_subset_iff.mpr (Set.mem_univ 0))
  rw [tendstoUniformlyOn_singleton_iff_tendsto] at h1
  have hcont_eval : Continuous
      (fun D : ℝ [×1]→L[ℝ] (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) =>
        ((D (fun _ : Fin 1 ↦ (1 : ℝ))) (1 : ℝ)) (1 : ℝ)) := by
    fun_prop
  have hlim := (hcont_eval.tendsto _).comp h1
  simp only [Function.comp_def, pin_deriv_one, flat_deriv_zero] at hlim
  have hconst1 : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique hconst1 hlim
  exact one_ne_zero h10

/-- The `C^0` and `C^1` topologies differ. -/
theorem ckTopology_ne :
    Manifold.metricCkTopology 𝓘(ℝ, ℝ) ℝ 0 ≠
      Manifold.metricCkTopology 𝓘(ℝ, ℝ) ℝ 1 := by
  intro h
  have h0 := wobble_tendsto_C0
  rw [h] at h0
  exact wobble_not_tendsto_C1 h0

end MetricCkTopologyTests
