/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Order.Zorn

/-!
# Multiplication form of the spectral theorem

This file constructs scalar spectral measures for bounded self-adjoint operators, realizes their
cyclic subspaces as `L²` spaces, and combines a maximal orthogonal family of cyclic subspaces into
the multiplication-operator form of the spectral theorem.
-/

@[expose] public section

open MeasureTheory
open scoped CompactlySupported ComplexOrder ENNReal

noncomputable section

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

universe u

private def spectralMulOfReal {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) : C(X, ℂ) :=
  (⟨Complex.ofReal, Complex.continuous_ofReal⟩ : C(ℝ, ℂ)).comp f

@[simp] private theorem spectralMulOfReal_apply {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) (x : X) : spectralMulOfReal f x = f x :=
  rfl

private def spectralMulOfRealL (X : Type*) [TopologicalSpace X] :
    C(X, ℝ) →ₗ[ℝ] C(X, ℂ) where
  toFun := spectralMulOfReal
  map_add' f g := by
    ext x
    simp
  map_smul' r f := by
    ext x
    simp

private noncomputable def spectralMulFunctional
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    C_c((spectrum ℂ T), ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f =>
        Complex.re (inner ℂ ((cfcHom hT.isStarNormal)
          (spectralMulOfRealL (spectrum ℂ T) f.toContinuousMap) v) v)
      map_add' := by
        intro f g
        have hfg : spectralMulOfRealL (spectrum ℂ T) (f + g).toContinuousMap =
            spectralMulOfRealL (spectrum ℂ T) f.toContinuousMap +
              spectralMulOfRealL (spectrum ℂ T) g.toContinuousMap := by
          ext x
          change (((f + g) x : ℝ) : ℂ) = (f x : ℂ) + (g x : ℂ)
          simp
        rw [hfg, map_add, add_apply, inner_add_left]
        exact Complex.add_re _ _
      map_smul' := by
        intro r f
        have hrf : spectralMulOfRealL (spectrum ℂ T) (r • f).toContinuousMap =
            (r : ℂ) • spectralMulOfRealL (spectrum ℂ T) f.toContinuousMap := by
          ext x
          change (((r • f) x : ℝ) : ℂ) = (r : ℂ) * (f x : ℂ)
          simp
        rw [hrf, map_smul, smul_apply, inner_smul_left]
        simp }
    (fun f hf => by
      have hfc : 0 ≤ spectralMulOfRealL (spectrum ℂ T) f.toContinuousMap := by
        intro x
        exact Complex.zero_le_real.mpr (hf x)
      have hop : 0 ≤ (cfcHom hT.isStarNormal)
          (spectralMulOfRealL (spectrum ℂ T) f.toContinuousMap) :=
        (cfcHom_nonneg_iff hT.isStarNormal).mpr hfc
      exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hop).re_inner_nonneg_left v)

@[simp] private theorem spectralMulFunctional_apply
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (f : C_c((spectrum ℂ T), ℝ)) :
    spectralMulFunctional T hT v f = Complex.re (inner ℂ ((cfcHom hT.isStarNormal)
      (spectralMulOfRealL (spectrum ℂ T) f.toContinuousMap) v) v) :=
  rfl

/-- **Scalar spectral measure of a vector.** Let $E$ be a complex Hilbert space, $T$ a bounded
self-adjoint operator on $E$ and $v \in E$. There is a finite regular measure $\mu$ on the
spectrum $\sigma(T) \subseteq \mathbb{C}$ of $T$ such that for every continuous function
$f : \sigma(T) \to \mathbb{R}$,
$\int_{\sigma(T)} f \, d\mu = \operatorname{Re} \langle f(T) v, v \rangle$, where $f(T)$ is the
continuous functional calculus of $T$ applied to $f$ viewed as a complex-valued function.

The measure lives on the complex spectrum. Its support is real because the spectrum of a
self-adjoint operator is real. -/
theorem IsSelfAdjoint.exists_spectralMeasure
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    ∃ μ : Measure (spectrum ℂ T), IsFiniteMeasure μ ∧ μ.Regular ∧
      ∀ f : C(spectrum ℂ T, ℝ),
        ∫ z, f z ∂μ = Complex.re (inner ℂ ((cfcHom hT.isStarNormal)
          (⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ :
            C(spectrum ℂ T, ℂ)) v) v) := by
  let Λ := spectralMulFunctional T hT v
  let μ := RealRMK.rieszMeasure Λ
  refine ⟨μ, inferInstance, inferInstance, ?_⟩
  intro f
  let f' : C_c((spectrum ℂ T), ℝ) :=
    CompactlySupportedContinuousMap.continuousMapEquiv f
  have h := RealRMK.integral_rieszMeasure Λ f'
  have hmap : spectralMulOfRealL (spectrum ℂ T) f'.toContinuousMap =
      (⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ :
        C(spectrum ℂ T, ℂ)) := by
    ext z
    rfl
  rw [← hmap]
  simpa [μ, Λ, f'] using h

private noncomputable def spectralMulMeasure
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) : Measure (spectrum ℂ T) :=
  (hT.exists_spectralMeasure T v).choose

private noncomputable instance spectralMulMeasureIsFinite
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    IsFiniteMeasure (spectralMulMeasure T hT v) :=
  (hT.exists_spectralMeasure T v).choose_spec.1

private noncomputable instance spectralMulMeasureRegular
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    (spectralMulMeasure T hT v).Regular :=
  (hT.exists_spectralMeasure T v).choose_spec.2.1

private theorem spectralMul_integral_measure
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (f : C(spectrum ℂ T, ℝ)) :
    ∫ z, f z ∂spectralMulMeasure T hT v =
      Complex.re (inner ℂ ((cfcHom hT.isStarNormal)
        (⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ :
          C(spectrum ℂ T, ℂ)) v) v) :=
  (hT.exists_spectralMeasure T v).choose_spec.2.2 f

private def spectralMulCfcMap
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    C(spectrum ℂ T, ℂ) →ₗ[ℂ] E where
  toFun f := (cfcHom hT.isStarNormal) f v
  map_add' f g := by simp
  map_smul' c f := by simp

private theorem spectralMulCfcMap_norm
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (f : C(spectrum ℂ T, ℂ)) :
    ‖spectralMulCfcMap T hT v f‖ =
      ‖ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f‖ := by
  let A := (cfcHom hT.isStarNormal) f
  let q : C(spectrum ℂ T, ℝ) :=
    ⟨fun z => Complex.normSq (f z), Complex.continuous_normSq.comp f.continuous⟩
  have hq :
      (⟨fun z => (q z : ℂ), Complex.continuous_ofReal.comp q.continuous⟩ :
        C(spectrum ℂ T, ℂ)) = star f * f := by
    ext z
    exact Complex.normSq_eq_conj_mul_self
  have hm := spectralMul_integral_measure T hT v q
  rw [hq, map_mul, map_star] at hm
  have hadj : inner ℂ ((star A * A) v) v = inner ℂ (A v) (A v) := by
    rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  apply (sq_eq_sq₀ (norm_nonneg (spectralMulCfcMap T hT v f))
    (norm_nonneg (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f))).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) (spectralMulCfcMap T hT v f),
    norm_sq_eq_re_inner (𝕜 := ℂ)
      (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f)]
  change (inner ℂ (spectralMulCfcMap T hT v f)
      (spectralMulCfcMap T hT v f)).re =
    (inner ℂ (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f)
      (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f)).re
  calc
    (inner ℂ (spectralMulCfcMap T hT v f)
        (spectralMulCfcMap T hT v f)).re =
        ∫ z, q z ∂spectralMulMeasure T hT v := by
      rw [show spectralMulCfcMap T hT v f = A v from rfl, ← hadj]
      exact hm.symm
    _ = (∫ z, f z * starRingEnd ℂ (f z) ∂spectralMulMeasure T hT v).re := by
      rw [show (fun z => f z * starRingEnd ℂ (f z)) =
          fun z => (q z : ℂ) by
        funext z
        exact Complex.mul_conj (f z)]
      have hi :
          (∫ z, (q z : ℂ) ∂spectralMulMeasure T hT v) =
            ((∫ z, q z ∂spectralMulMeasure T hT v : ℝ) : ℂ) := by
        exact integral_ofReal
      rw [hi]
      simp
    _ = (inner ℂ
        (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f)
        (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f)).re := by
      rw [MeasureTheory.ContinuousMap.inner_toLp]

private noncomputable def spectralMulCyclicIsometry
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    Lp ℂ 2 (spectralMulMeasure T hT v) →ₗᵢ[ℂ] E :=
  (spectralMulCfcMap T hT v).extendOfIsometry
    (ContinuousMap.toLp_denseRange ℂ (spectralMulMeasure T hT v) ℂ (by norm_num))
    (spectralMulCfcMap_norm T hT v)

@[simp] private theorem spectralMulCyclicIsometry_toLp
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (f : C(spectrum ℂ T, ℂ)) :
    spectralMulCyclicIsometry T hT v
        (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f) =
      (cfcHom hT.isStarNormal) f v := by
  exact LinearMap.extendOfIsometry_eq
    (f := spectralMulCfcMap T hT v)
    (e := (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ).toLinearMap)
    (ContinuousMap.toLp_denseRange ℂ (spectralMulMeasure T hT v) ℂ (by norm_num))
    (spectralMulCfcMap_norm T hT v) f

private def spectralMulCoordinate
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) : C(spectrum ℂ T, ℂ) :=
  ContinuousMap.restrict (spectrum ℂ T) (ContinuousMap.id ℂ)

private noncomputable def spectralMulCoordinateLp
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    Lp ℂ ∞ (spectralMulMeasure T hT v) :=
  BoundedContinuousFunction.toLp ∞ (spectralMulMeasure T hT v) ℂ
    (ContinuousMap.equivBoundedOfCompact (spectrum ℂ T) ℂ (spectralMulCoordinate T))

private theorem spectralMulCoordinateLp_ae
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    spectralMulCoordinateLp T hT v =ᵐ[spectralMulMeasure T hT v]
      fun z => (z : ℂ) := by
  exact BoundedContinuousFunction.coeFn_toLp ∞ (spectralMulMeasure T hT v) ℂ
    (ContinuousMap.equivBoundedOfCompact (spectrum ℂ T) ℂ (spectralMulCoordinate T))

private noncomputable def spectralMulLpOperator
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    Lp ℂ 2 (spectralMulMeasure T hT v) →L[ℂ]
      Lp ℂ 2 (spectralMulMeasure T hT v) :=
  LinearMap.mkContinuous
    { toFun := fun g => spectralMulCoordinateLp T hT v • g
      map_add' := fun g₁ g₂ => Lp.add_smul _ _ _
      map_smul' := fun c g => by
        change spectralMulCoordinateLp T hT v • (c • g) =
          c • (spectralMulCoordinateLp T hT v • g)
        exact (Lp.smul_comm (p := ∞) (q := 2) (r := 2) c
          (spectralMulCoordinateLp T hT v) g).symm }
    ‖spectralMulCoordinateLp T hT v‖
    (fun g => Lp.norm_smul_le (spectralMulCoordinateLp T hT v) g)

private theorem spectralMulLpOperator_toLp
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (f : C(spectrum ℂ T, ℂ)) :
    spectralMulLpOperator T hT v
        (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f) =
      ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ
        (spectralMulCoordinate T * f) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (spectralMulCoordinateLp T hT v)
      (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f),
    spectralMulCoordinateLp_ae T hT v,
    f.coeFn_toLp (p := 2) (𝕜 := ℂ) (spectralMulMeasure T hT v),
    (spectralMulCoordinate T * f).coeFn_toLp (p := 2) (𝕜 := ℂ)
      (spectralMulMeasure T hT v)] with z hmul hc hf hcf
  change _ = (spectralMulCoordinate T * f : C(spectrum ℂ T, ℂ)) z at hcf
  have hprod : (spectralMulCoordinateLp T hT v) z *
      (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f) z =
      (z : ℂ) * f z := congrArg₂ (· * ·) hc hf
  simpa [spectralMulLpOperator, spectralMulCoordinate, Pi.smul_apply, smul_eq_mul]
    using hmul.trans hprod |>.trans hcf.symm

private theorem spectralMulCyclicIsometry_intertwines
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (g : Lp ℂ 2 (spectralMulMeasure T hT v)) :
    spectralMulCyclicIsometry T hT v (spectralMulLpOperator T hT v g) =
      T (spectralMulCyclicIsometry T hT v g) := by
  refine (ContinuousMap.toLp_denseRange ℂ (spectralMulMeasure T hT v) ℂ
    (by norm_num)).induction ?_ (isClosed_eq (by fun_prop) (by fun_prop)) g
  rintro y ⟨f, rfl⟩
  rw [spectralMulLpOperator_toLp, spectralMulCyclicIsometry_toLp,
    spectralMulCyclicIsometry_toLp, map_mul, spectralMulCoordinate, cfcHom_id,
    mul_apply_eq_comp]

private noncomputable def spectralMulCyclicSubspace
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) : Submodule ℂ E :=
  LinearMap.range (spectralMulCyclicIsometry T hT v).toLinearMap

private theorem spectralMul_cfc_mem_cyclicSubspace
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (f : C(spectrum ℂ T, ℂ)) :
    (cfcHom hT.isStarNormal) f v ∈ spectralMulCyclicSubspace T hT v := by
  exact ⟨ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f,
    spectralMulCyclicIsometry_toLp T hT v f⟩

private theorem spectralMul_mem_cyclicSubspace
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    v ∈ spectralMulCyclicSubspace T hT v := by
  simpa using spectralMul_cfc_mem_cyclicSubspace T hT v (1 : C(spectrum ℂ T, ℂ))

private theorem spectralMulCyclicSubspace_isOrtho
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) {v w : E}
    (hw : w ∈ (spectralMulCyclicSubspace T hT v)ᗮ) :
    spectralMulCyclicSubspace T hT w ⟂ spectralMulCyclicSubspace T hT v := by
  rw [Submodule.isOrtho_iff_le]
  rintro _ ⟨g, rfl⟩
  refine (ContinuousMap.toLp_denseRange ℂ (spectralMulMeasure T hT w) ℂ
    (by norm_num)).induction ?_
      ((spectralMulCyclicSubspace T hT v).isClosed_orthogonal.preimage
        (spectralMulCyclicIsometry T hT w).continuous) g
  rintro _ ⟨f, rfl⟩
  change spectralMulCyclicIsometry T hT w
    (ContinuousMap.toLp 2 (spectralMulMeasure T hT w) ℂ f) ∈ _
  rw [spectralMulCyclicIsometry_toLp]
  apply (Submodule.mem_orthogonal' (spectralMulCyclicSubspace T hT v) _).mpr
  rintro _ ⟨q, rfl⟩
  change inner ℂ ((cfcHom hT.isStarNormal) f w)
    (spectralMulCyclicIsometry T hT v q) = 0
  refine (ContinuousMap.toLp_denseRange ℂ (spectralMulMeasure T hT v) ℂ
    (by norm_num)).induction ?_
      (isClosed_eq (continuous_const.inner (spectralMulCyclicIsometry T hT v).continuous)
        continuous_const) q
  rintro _ ⟨k, rfl⟩
  rw [spectralMulCyclicIsometry_toLp]
  let A := (cfcHom hT.isStarNormal) f
  let B := (cfcHom hT.isStarNormal) k
  calc
    inner ℂ (A w) (B v) = inner ℂ w (ContinuousLinearMap.adjoint A (B v)) :=
      (ContinuousLinearMap.adjoint_inner_right A w (B v)).symm
    _ = inner ℂ w ((cfcHom hT.isStarNormal) (star f * k) v) := by
      rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp]
    _ = 0 := (Submodule.mem_orthogonal' (spectralMulCyclicSubspace T hT v) w).mp hw _
      (spectralMul_cfc_mem_cyclicSubspace T hT v (star f * k))

private def spectralMulAdmissible
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (S : Set E) : Prop :=
  S.Pairwise fun v w =>
    spectralMulCyclicSubspace T hT v ⟂ spectralMulCyclicSubspace T hT w

private theorem spectralMul_exists_maximalAdmissible
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    ∃ S : Set E, spectralMulAdmissible T hT S ∧
      ∀ S' : Set E, spectralMulAdmissible T hT S' → S ⊆ S' → S = S' := by
  obtain ⟨S, hS⟩ := zorn_subset {S : Set E | spectralMulAdmissible T hT S} (by
    intro c hc hchain
    refine ⟨⋃₀ c, ?_, ?_⟩
    · rintro x hx y hy hxy
      obtain ⟨sx, hsxc, hxs⟩ := Set.mem_sUnion.mp hx
      obtain ⟨sy, hsyc, hys⟩ := Set.mem_sUnion.mp hy
      rcases hchain.total (x := sx) (y := sy) hsxc hsyc with hsxy | hsyx
      · exact (hc hsyc) (x := x) (hsxy hxs) (y := y) hys hxy
      · exact (hc hsxc) (x := x) hxs (y := y) (hsyx hys) hxy
    · intro s hs
      exact Set.subset_sUnion_of_mem hs)
  exact ⟨S, hS.prop, fun S' hS' hsub => hS.eq_of_le hS' hsub⟩

private noncomputable def spectralMulIndexSet
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) : Set E :=
  (spectralMul_exists_maximalAdmissible T hT).choose

private theorem spectralMulIndexSet_admissible
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    spectralMulAdmissible T hT (spectralMulIndexSet T hT) :=
  (spectralMul_exists_maximalAdmissible T hT).choose_spec.1

private theorem spectralMulIndexSet_maximal
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (S : Set E)
    (hS : spectralMulAdmissible T hT S)
    (hsub : spectralMulIndexSet T hT ⊆ S) : spectralMulIndexSet T hT = S :=
  (spectralMul_exists_maximalAdmissible T hT).choose_spec.2 S hS hsub

private theorem spectralMulIndexSet_total
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    (⨆ i : spectralMulIndexSet T hT, spectralMulCyclicSubspace T hT (i : E))ᗮ = ⊥ := by
  let K := ⨆ i : spectralMulIndexSet T hT, spectralMulCyclicSubspace T hT (i : E)
  rw [Submodule.eq_bot_iff]
  intro w hw
  by_contra hw0
  have hadd : spectralMulAdmissible T hT (insert w (spectralMulIndexSet T hT)) := by
    rw [spectralMulAdmissible, Set.pairwise_insert]
    refine ⟨spectralMulIndexSet_admissible T hT, ?_⟩
    intro v hvS hwv
    have hZvK : spectralMulCyclicSubspace T hT v ≤ K :=
      le_iSup (fun i : spectralMulIndexSet T hT =>
        spectralMulCyclicSubspace T hT (i : E)) ⟨v, hvS⟩
    have hwZv : w ∈ (spectralMulCyclicSubspace T hT v)ᗮ :=
      (Submodule.orthogonal_le hZvK) hw
    have h := spectralMulCyclicSubspace_isOrtho T hT hwZv
    exact ⟨h, h.symm⟩
  have heq := spectralMulIndexSet_maximal T hT _ hadd
    (Set.subset_insert w (spectralMulIndexSet T hT))
  have hwS : w ∈ spectralMulIndexSet T hT := by
    rw [heq]
    exact Set.mem_insert w _
  have hwK : w ∈ K :=
    (le_iSup (fun i : spectralMulIndexSet T hT =>
      spectralMulCyclicSubspace T hT (i : E)) ⟨w, hwS⟩)
      (spectralMul_mem_cyclicSubspace T hT w)
  exact hw0 (inner_self_eq_zero.mp ((Submodule.mem_orthogonal K w).mp hw w hwK))

private theorem spectralMulOrthogonalFamily
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    OrthogonalFamily ℂ
      (fun i : spectralMulIndexSet T hT => Lp ℂ 2 (spectralMulMeasure T hT (i : E)))
      (fun i => spectralMulCyclicIsometry T hT (i : E)) := by
  intro i j hij x y
  have h := spectralMulIndexSet_admissible T hT i.property j.property
    (Subtype.coe_ne_coe.mpr hij)
  exact h.inner_eq (LinearMap.mem_range_self _ x) (LinearMap.mem_range_self _ y)

private theorem spectralMulIsHilbertSum
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    IsHilbertSum ℂ
      (fun i : spectralMulIndexSet T hT => Lp ℂ 2 (spectralMulMeasure T hT (i : E)))
      (fun i => spectralMulCyclicIsometry T hT (i : E)) := by
  apply IsHilbertSum.mk (spectralMulOrthogonalFamily T hT)
  let K := ⨆ i : spectralMulIndexSet T hT, spectralMulCyclicSubspace T hT (i : E)
  have hK : Kᗮ = ⊥ := spectralMulIndexSet_total T hT
  have hclosure : K.topologicalClosure = ⊤ := by
    rw [← K.orthogonal_orthogonal_eq_closure, hK, Submodule.bot_orthogonal_eq_top]
  rw [show (⨆ i : spectralMulIndexSet T hT,
      LinearMap.range (spectralMulCyclicIsometry T hT (i : E)).toLinearMap) = K from rfl,
    hclosure]

private abbrev spectralMulSpace
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :=
  spectralMulIndexSet T hT × spectrum ℂ T

private noncomputable instance spectralMulIndexMeasurableSpace
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    MeasurableSpace (spectralMulIndexSet T hT) := ⊤

private noncomputable instance spectralMulMeasurableSpace
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) : MeasurableSpace (spectralMulSpace T hT) := by
  exact inferInstance

private def spectralMulFiber
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT) :
    Set (spectralMulSpace T hT) := {x | x.1 = i}

private noncomputable def spectralMulFiberMeasure
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT) :
    Measure (spectralMulSpace T hT) := by
  exact Measure.map (Prod.mk i) (spectralMulMeasure T hT (i : E))

private noncomputable def spectralMulSumMeasure
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    Measure (spectralMulSpace T hT) := by
  exact Measure.sum (spectralMulFiberMeasure T hT)

private theorem spectralMulFiber_measurableSet
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT) :
    MeasurableSet (spectralMulFiber T hT i) := by
  exact (measurable_fst (β := spectrum ℂ T) (α := spectralMulIndexSet T hT))
    (MeasurableSet.singleton i)

private theorem spectralMulSumMeasure_restrict_fiber
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT) :
    (spectralMulSumMeasure T hT).restrict (spectralMulFiber T hT i) =
      spectralMulFiberMeasure T hT i := by
  ext s hs
  rw [Measure.restrict_apply hs,
    spectralMulSumMeasure, Measure.sum_apply _ (hs.inter (spectralMulFiber_measurableSet T hT i))]
  classical
  rw [tsum_eq_single i]
  · rw [spectralMulFiberMeasure, Measure.map_apply measurable_prodMk_left
      (hs.inter (spectralMulFiber_measurableSet T hT i)),
      Measure.map_apply measurable_prodMk_left hs]
    congr 1
    ext z
    simp [spectralMulFiber]
  · intro j hji
    rw [spectralMulFiberMeasure, Measure.map_apply measurable_prodMk_left
      (hs.inter (spectralMulFiber_measurableSet T hT i))]
    simp [spectralMulFiber, hji]

private def spectralMulExtend
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT)
    (f : spectrum ℂ T → ℂ) : spectralMulSpace T hT → ℂ :=
  (spectralMulFiber T hT i).indicator fun x => f x.2

private theorem spectralMulExtend_eLpNorm
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT)
    (f : spectrum ℂ T → ℂ) :
    eLpNorm (spectralMulExtend T hT i f) 2 (spectralMulSumMeasure T hT) =
      eLpNorm f 2 (spectralMulMeasure T hT (i : E)) := by
  rw [spectralMulExtend, eLpNorm_indicator_eq_eLpNorm_restrict
      (spectralMulFiber_measurableSet T hT i).nullMeasurableSet,
    spectralMulSumMeasure_restrict_fiber, spectralMulFiberMeasure,
    (measurableEmbedding_prodMk_left i).eLpNorm_map_measure]
  rfl

private theorem spectralMulExtend_congr_ae
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT)
    {f g : spectrum ℂ T → ℂ} (hfg : f =ᵐ[spectralMulMeasure T hT (i : E)] g) :
    spectralMulExtend T hT i f =ᵐ[spectralMulSumMeasure T hT]
      spectralMulExtend T hT i g := by
  apply ae_of_ae_restrict_of_ae_restrict_compl (spectralMulFiber T hT i)
  · rw [spectralMulSumMeasure_restrict_fiber, spectralMulFiberMeasure]
    apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
    filter_upwards [hfg] with z hz
    simpa [spectralMulExtend, spectralMulFiber] using hz
  · apply (ae_restrict_iff' (spectralMulFiber_measurableSet T hT i).compl).mpr
    filter_upwards with x hx
    have hxi : x.1 ≠ i := by simpa [spectralMulFiber] using hx
    simp [spectralMulExtend, spectralMulFiber, hxi]

private theorem spectralMulExtend_memLp
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT)
    (f : Lp ℂ 2 (spectralMulMeasure T hT (i : E))) :
    MemLp (spectralMulExtend T hT i f) 2 (spectralMulSumMeasure T hT) := by
  rw [memLp_iff, spectralMulExtend_eLpNorm]
  exact Lp.eLpNorm_lt_top f

set_option maxHeartbeats 800000 in
-- Elaborating the dependent `L²` fiber extension needs a larger heartbeat budget.
private noncomputable def spectralMulFiberIsometry
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT) :
    Lp ℂ 2 (spectralMulMeasure T hT (i : E)) →ₗᵢ[ℂ]
      Lp ℂ 2 (spectralMulSumMeasure T hT) := by
  refine
    { toFun := fun f => (spectralMulExtend_memLp T hT i f).toLp
        (spectralMulExtend T hT i f)
      map_add' := ?_
      map_smul' := ?_
      norm_map' := ?_ }
  · intro f g
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i (f + g)),
      MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i f),
      MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i g),
      Lp.coeFn_add ((spectralMulExtend_memLp T hT i f).toLp
        (spectralMulExtend T hT i f))
        ((spectralMulExtend_memLp T hT i g).toLp (spectralMulExtend T hT i g)),
      spectralMulExtend_congr_ae T hT i (Lp.coeFn_add f g)] with x hfg hf hg hadd hin
    rw [hfg, hadd, Pi.add_apply, hf, hg, hin]
    by_cases hx : x ∈ spectralMulFiber T hT i
    · simp [spectralMulExtend, Set.indicator_of_mem hx]
    · simp [spectralMulExtend, Set.indicator_of_notMem hx]
  · intro c f
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i (c • f)),
      MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i f),
      Lp.coeFn_smul c ((spectralMulExtend_memLp T hT i f).toLp
        (spectralMulExtend T hT i f)),
      spectralMulExtend_congr_ae T hT i (Lp.coeFn_smul c f)] with x hcf hf hsmul hin
    rw [hcf, show (RingHom.id ℂ) c = c from rfl, hsmul, Pi.smul_apply, hf, hin]
    by_cases hx : x ∈ spectralMulFiber T hT i
    · simp [spectralMulExtend, Set.indicator_of_mem hx]
    · simp [spectralMulExtend, Set.indicator_of_notMem hx]
  · intro f
    change ‖(spectralMulExtend_memLp T hT i f).toLp
      (spectralMulExtend T hT i f)‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def,
      eLpNorm_congr_ae (MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i f)),
      spectralMulExtend_eLpNorm]

private theorem spectralMulFiberOrthogonalFamily
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    OrthogonalFamily ℂ
      (fun i : spectralMulIndexSet T hT => Lp ℂ 2 (spectralMulMeasure T hT (i : E)))
      (spectralMulFiberIsometry T hT) := by
  intro i j hij f g
  rw [L2.inner_def, ← integral_zero]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i f),
    MemLp.coeFn_toLp (spectralMulExtend_memLp T hT j g)] with x hf hg
  change inner ℂ
    ((((spectralMulExtend_memLp T hT i f).toLp
      (spectralMulExtend T hT i f)) : spectralMulSpace T hT → ℂ) x)
    ((((spectralMulExtend_memLp T hT j g).toLp
      (spectralMulExtend T hT j g)) : spectralMulSpace T hT → ℂ) x) = 0
  rw [hf, hg]
  by_cases hi : x.1 = i
  · have hj : x.1 ≠ j := fun hj => hij (hi.symm.trans hj)
    have hxi : x ∈ spectralMulFiber T hT i := hi
    have hxj : x ∉ spectralMulFiber T hT j := hj
    simp [spectralMulExtend, Set.indicator_of_mem hxi, Set.indicator_of_notMem hxj]
  · have hxi : x ∉ spectralMulFiber T hT i := hi
    simp [spectralMulExtend, Set.indicator_of_notMem hxi]

private theorem spectralMulFiber_ae_zero_of_mem_orthogonal
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (F : Lp ℂ 2 (spectralMulSumMeasure T hT))
    (hF : F ∈ (⨆ i : spectralMulIndexSet T hT,
      LinearMap.range (spectralMulFiberIsometry T hT i).toLinearMap)ᗮ)
    (i : spectralMulIndexSet T hT) :
    ∀ᵐ z ∂spectralMulMeasure T hT (i : E), F (i, z) = 0 := by
  have hFrestrict :
      MemLp (F : spectralMulSpace T hT → ℂ) 2 (spectralMulFiberMeasure T hT i) :=
    MemLp.mono_measure
      (by
        rw [spectralMulSumMeasure]
        exact Measure.le_sum _ i)
      (Lp.memLp F)
  have hFcomp : MemLp (fun z => F (i, z)) 2 (spectralMulMeasure T hT (i : E)) := by
    have hmap : MemLp (F : spectralMulSpace T hT → ℂ) 2
        (Measure.map (Prod.mk i) (spectralMulMeasure T hT (i : E))) := by
      simpa [spectralMulFiberMeasure] using hFrestrict
    have hcomp := (measurableEmbedding_prodMk_left i).memLp_map_measure_iff.mp hmap
    simpa [Function.comp_def] using hcomp
  let g : Lp ℂ 2 (spectralMulMeasure T hT (i : E)) :=
    hFcomp.toLp (fun z => F (i, z))
  have hg : (g : spectrum ℂ T → ℂ) =ᵐ[spectralMulMeasure T hT (i : E)]
      fun z => F (i, z) := by
    exact MemLp.coeFn_toLp hFcomp
  have hJ :
      ((spectralMulFiberIsometry T hT i g : Lp ℂ 2 (spectralMulSumMeasure T hT)) :
          spectralMulSpace T hT → ℂ) =ᵐ[spectralMulSumMeasure T hT]
        spectralMulExtend T hT i (fun z => F (i, z)) := by
    exact (MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i g)).trans
      (spectralMulExtend_congr_ae T hT i hg)
  have hinner : inner ℂ F (spectralMulFiberIsometry T hT i g) = 0 := by
    exact ((⨆ i : spectralMulIndexSet T hT,
      LinearMap.range (spectralMulFiberIsometry T hT i).toLinearMap).mem_orthogonal' F).mp
        hF _ ((le_iSup (fun i : spectralMulIndexSet T hT =>
          LinearMap.range (spectralMulFiberIsometry T hT i).toLinearMap) i)
            (LinearMap.mem_range_self _ g))
  have hinner_self :
      inner ℂ (spectralMulFiberIsometry T hT i g)
          (spectralMulFiberIsometry T hT i g) =
        inner ℂ F (spectralMulFiberIsometry T hT i g) := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hJ] with x hx
    rw [hx]
    rcases x with ⟨j, z⟩
    by_cases hji : j = i
    · subst j
      simp [spectralMulExtend, spectralMulFiber]
    · simp [spectralMulExtend, spectralMulFiber, hji]
  have hJzero : spectralMulFiberIsometry T hT i g = 0 :=
    inner_self_eq_zero.mp (hinner_self.trans hinner)
  have hgzero : g = 0 := by
    apply (spectralMulFiberIsometry T hT i).injective
    simpa using hJzero
  rw [hgzero] at hg
  filter_upwards [hg, Lp.coeFn_zero ℂ 2 (spectralMulMeasure T hT (i : E))] with z hz hz0
  rw [← hz]
  exact hz0

private theorem spectralMulFiber_iSup_orthogonal_eq_bot
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    (⨆ i : spectralMulIndexSet T hT,
      LinearMap.range (spectralMulFiberIsometry T hT i).toLinearMap)ᗮ = ⊥ := by
  apply le_antisymm
  · intro F hF
    rw [Submodule.mem_bot]
    apply Lp.ext
    have hmeas : MeasurableSet
        {x : spectralMulSpace T hT | (F : spectralMulSpace T hT → ℂ) x = 0} := by
      exact (MeasurableSet.singleton 0).preimage (Lp.stronglyMeasurable F).measurable
    have hzero : ∀ᵐ x ∂spectralMulSumMeasure T hT, F x = 0 := by
      change ∀ᵐ x ∂Measure.sum (spectralMulFiberMeasure T hT), F x = 0
      rw [Measure.ae_sum_iff' hmeas]
      intro i
      rw [spectralMulFiberMeasure]
      apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
      exact spectralMulFiber_ae_zero_of_mem_orthogonal T hT F hF i
    filter_upwards [hzero,
      Lp.coeFn_zero ℂ 2 (spectralMulSumMeasure T hT)] with x hx hx0
    rw [hx]
    simpa using hx0.symm
  · exact bot_le

private theorem spectralMulFiberIsHilbertSum
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    IsHilbertSum ℂ
      (fun i : spectralMulIndexSet T hT => Lp ℂ 2 (spectralMulMeasure T hT (i : E)))
      (spectralMulFiberIsometry T hT) := by
  apply IsHilbertSum.mk (spectralMulFiberOrthogonalFamily T hT)
  let K : Submodule ℂ (Lp ℂ 2 (spectralMulSumMeasure T hT)) :=
    ⨆ i : spectralMulIndexSet T hT,
      LinearMap.range (spectralMulFiberIsometry T hT i).toLinearMap
  have hK : Kᗮ = ⊥ := spectralMulFiber_iSup_orthogonal_eq_bot T hT
  have hclosure : K.topologicalClosure = ⊤ := by
    rw [← K.orthogonal_orthogonal_eq_closure, hK]
    simp
  exact hclosure.ge

private theorem spectralMulLpOperator_ae
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (g : Lp ℂ 2 (spectralMulMeasure T hT v)) :
    spectralMulLpOperator T hT v g =ᵐ[spectralMulMeasure T hT v]
      fun z => (z : ℂ) * g z := by
  change (spectralMulCoordinateLp T hT v • g :
    Lp ℂ 2 (spectralMulMeasure T hT v)) =ᵐ[spectralMulMeasure T hT v] _
  filter_upwards [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (spectralMulCoordinateLp T hT v) g,
    spectralMulCoordinateLp_ae T hT v] with z hmul hz
  rw [hmul]
  change (spectralMulCoordinateLp T hT v) z * g z = (z : ℂ) * g z
  rw [hz]

private def spectralMulGlobalCoordinate
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) : spectralMulSpace T hT → ℂ :=
  fun x => x.2

private theorem spectralMulGlobalCoordinate_measurable
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    Measurable (spectralMulGlobalCoordinate T hT) := by
  exact measurable_subtype_coe.comp measurable_snd

private theorem spectralMulGlobalCoordinate_memLp
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    MemLp (spectralMulGlobalCoordinate T hT) ∞ (spectralMulSumMeasure T hT) := by
  apply memLp_top_of_bound
    (spectralMulGlobalCoordinate_measurable T hT).stronglyMeasurable.aestronglyMeasurable
    ‖spectralMulCoordinate T‖
  filter_upwards with x
  exact ContinuousMap.norm_coe_le_norm (spectralMulCoordinate T) x.2

private noncomputable def spectralMulGlobalCoordinateLp
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    Lp ℂ ∞ (spectralMulSumMeasure T hT) :=
  (spectralMulGlobalCoordinate_memLp T hT).toLp (spectralMulGlobalCoordinate T hT)

private theorem spectralMulGlobalCoordinateLp_ae
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    spectralMulGlobalCoordinateLp T hT =ᵐ[spectralMulSumMeasure T hT]
      spectralMulGlobalCoordinate T hT := by
  exact MemLp.coeFn_toLp (spectralMulGlobalCoordinate_memLp T hT)

private noncomputable def spectralMulGlobalLpOperator
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    Lp ℂ 2 (spectralMulSumMeasure T hT) →L[ℂ]
      Lp ℂ 2 (spectralMulSumMeasure T hT) :=
  LinearMap.mkContinuous
    { toFun := fun g => spectralMulGlobalCoordinateLp T hT • g
      map_add' := fun g₁ g₂ => Lp.add_smul _ _ _
      map_smul' := fun c g => by
        change spectralMulGlobalCoordinateLp T hT • (c • g) =
          c • (spectralMulGlobalCoordinateLp T hT • g)
        exact (Lp.smul_comm (p := ∞) (q := 2) (r := 2) c
          (spectralMulGlobalCoordinateLp T hT) g).symm }
    ‖spectralMulGlobalCoordinateLp T hT‖
    (fun g => Lp.norm_smul_le (spectralMulGlobalCoordinateLp T hT) g)

private theorem spectralMulGlobalLpOperator_ae
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (g : Lp ℂ 2 (spectralMulSumMeasure T hT)) :
    spectralMulGlobalLpOperator T hT g =ᵐ[spectralMulSumMeasure T hT]
      fun x => (x.2 : ℂ) * g x := by
  change (spectralMulGlobalCoordinateLp T hT • g :
    Lp ℂ 2 (spectralMulSumMeasure T hT)) =ᵐ[spectralMulSumMeasure T hT] _
  filter_upwards [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (spectralMulGlobalCoordinateLp T hT) g,
    spectralMulGlobalCoordinateLp_ae T hT] with x hmul hx
  rw [hmul]
  change (spectralMulGlobalCoordinateLp T hT) x * g x = (x.2 : ℂ) * g x
  rw [hx]
  rfl

private theorem spectralMulGlobalLpOperator_fiber
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT)
    (g : Lp ℂ 2 (spectralMulMeasure T hT (i : E))) :
    spectralMulGlobalLpOperator T hT (spectralMulFiberIsometry T hT i g) =
      spectralMulFiberIsometry T hT i (spectralMulLpOperator T hT (i : E) g) := by
  apply Lp.ext
  filter_upwards [spectralMulGlobalLpOperator_ae T hT
      (spectralMulFiberIsometry T hT i g),
    MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i g),
    MemLp.coeFn_toLp
      (spectralMulExtend_memLp T hT i (spectralMulLpOperator T hT (i : E) g)),
    spectralMulExtend_congr_ae T hT i (spectralMulLpOperator_ae T hT (i : E) g)]
      with x hmul hg hMg hcongr
  rw [hmul]
  change (x.2 : ℂ) *
      ((((spectralMulExtend_memLp T hT i g).toLp
        (spectralMulExtend T hT i g)) : spectralMulSpace T hT → ℂ) x) =
    ((((spectralMulExtend_memLp T hT i (spectralMulLpOperator T hT (i : E) g)).toLp
        (spectralMulExtend T hT i (spectralMulLpOperator T hT (i : E) g))) :
          spectralMulSpace T hT → ℂ) x)
  rw [hg, hMg, hcongr]
  by_cases hx : x ∈ spectralMulFiber T hT i
  · simp [spectralMulExtend, Set.indicator_of_mem hx]
  · simp [spectralMulExtend, Set.indicator_of_notMem hx]

private noncomputable def spectralMulEquiv
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    E ≃ₗᵢ[ℂ] Lp ℂ 2 (spectralMulSumMeasure T hT) :=
  (spectralMulIsHilbertSum T hT).linearIsometryEquiv.trans
    (spectralMulFiberIsHilbertSum T hT).linearIsometryEquiv.symm

private theorem spectralMulEquiv_cyclic
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT)
    (g : Lp ℂ 2 (spectralMulMeasure T hT (i : E))) :
    spectralMulEquiv T hT (spectralMulCyclicIsometry T hT (i : E) g) =
      spectralMulFiberIsometry T hT i g := by
  classical
  rw [← (spectralMulIsHilbertSum T hT).linearIsometryEquiv_symm_apply_single g]
  change (spectralMulFiberIsHilbertSum T hT).linearIsometryEquiv.symm
      ((spectralMulIsHilbertSum T hT).linearIsometryEquiv
        ((spectralMulIsHilbertSum T hT).linearIsometryEquiv.symm (lp.single 2 i g))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,
    (spectralMulFiberIsHilbertSum T hT).linearIsometryEquiv_symm_apply_single]

private theorem spectralMulEquiv_intertwines
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (x : E) :
    spectralMulEquiv T hT (T x) =
      spectralMulGlobalLpOperator T hT (spectralMulEquiv T hT x) := by
  let A : E →L[ℂ] Lp ℂ 2 (spectralMulSumMeasure T hT) :=
    (spectralMulEquiv T hT).toLinearIsometry.toContinuousLinearMap.comp T
  let B : E →L[ℂ] Lp ℂ 2 (spectralMulSumMeasure T hT) :=
    (spectralMulGlobalLpOperator T hT).comp
      (spectralMulEquiv T hT).toLinearIsometry.toContinuousLinearMap
  let N : Submodule ℂ E := LinearMap.ker (A - B).toLinearMap
  let K : Submodule ℂ E :=
    ⨆ i : spectralMulIndexSet T hT,
      LinearMap.range (spectralMulCyclicIsometry T hT (i : E)).toLinearMap
  have hKN : K ≤ N := by
    apply iSup_le
    intro i
    rintro _ ⟨g, rfl⟩
    rw [LinearMap.mem_ker]
    change (A - B) (spectralMulCyclicIsometry T hT (i : E) g) = 0
    rw [sub_apply]
    dsimp [A, B]
    change spectralMulEquiv T hT
        (T (spectralMulCyclicIsometry T hT (i : E) g)) -
      spectralMulGlobalLpOperator T hT
        (spectralMulEquiv T hT (spectralMulCyclicIsometry T hT (i : E) g)) = 0
    rw [sub_eq_zero, ← spectralMulCyclicIsometry_intertwines,
      spectralMulEquiv_cyclic, spectralMulEquiv_cyclic,
      spectralMulGlobalLpOperator_fiber]
  have hKclosure : K.topologicalClosure = ⊤ := by
    have hKorth : Kᗮ = ⊥ := spectralMulIndexSet_total T hT
    rw [← K.orthogonal_orthogonal_eq_closure, hKorth,
      Submodule.bot_orthogonal_eq_top]
  have hNtop : N = ⊤ := by
    apply top_unique
    have hclosure_le : K.topologicalClosure ≤ N :=
      K.topologicalClosure_minimal hKN (A - B).isClosed_ker
    simpa [hKclosure] using hclosure_le
  have hxN : x ∈ N := by rw [hNtop]; exact Submodule.mem_top
  rw [LinearMap.mem_ker] at hxN
  change (A - B) x = 0 at hxN
  rw [sub_apply] at hxN
  dsimp [A, B] at hxN
  change spectralMulEquiv T hT (T x) -
    spectralMulGlobalLpOperator T hT (spectralMulEquiv T hT x) = 0 at hxN
  exact sub_eq_zero.mp hxN

namespace MathlibExt.Analysis.InnerProductSpace.BoundedSelfAdjointSpectralWanted

/--
**Spectral theorem for bounded self-adjoint operators, multiplication form.** Let $E$ be a
complex Hilbert space and $T$ a bounded self-adjoint operator on $E$. Then there are a measure
space $(X, \mu)$, a measurable function $\varphi : X \to \mathbb{R}$ and a linear isometric
isomorphism $U$ of $E$ onto $L^2(X, \mu; \mathbb{C})$ such that for every $x \in E$,
$U(Tx)(a) = \varphi(a)\,(Ux)(a)$ for $\mu$-almost every $a \in X$.

Proof: Scalar measures from the continuous functional calculus identify each cyclic subspace with an
$L^2$ space. A maximal orthogonal family of cyclic subspaces is then assembled over a disjoint-union
measure, where the spectral coordinate acts by multiplication.

Proves `Wanted` entry `boundedSelfAdjoint_spectral_multiplication`.

Sources: Mathlib
`Mathlib/Analysis/InnerProductSpace/Spectrum.lean` TODO (spectral theory for bounded
self-adjoint operators); W. Rudin, Functional Analysis, 2nd ed., Ch. 12.
-/
theorem boundedSelfAdjoint_spectral_multiplication
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    ∃ (X : Type u) (_ : MeasurableSpace X) (μ : Measure X) (φ : X → ℝ) (_ : Measurable φ)
      (U : E ≃ₗᵢ[ℂ] Lp ℂ 2 μ),
      ∀ x, ∀ᵐ a ∂μ, U (T x) a = (φ a : ℂ) * U x a := by
  refine ⟨spectralMulSpace T hT, spectralMulMeasurableSpace T hT,
    spectralMulSumMeasure T hT, (fun x => (x.2 : ℂ).re), ?_, spectralMulEquiv T hT, ?_⟩
  · exact Complex.measurable_re.comp (measurable_subtype_coe.comp measurable_snd)
  · intro x
    filter_upwards [spectralMulGlobalLpOperator_ae T hT (spectralMulEquiv T hT x)]
      with a ha
    rw [spectralMulEquiv_intertwines T hT x, ha]
    have him : (a.2 : ℂ).im = 0 := hT.im_eq_zero_of_mem_spectrum a.2.property
    have hz : (a.2 : ℂ) = ((a.2 : ℂ).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    rw [hz]
    simp

end MathlibExt.Analysis.InnerProductSpace.BoundedSelfAdjointSpectralWanted
