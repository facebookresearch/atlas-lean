/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Topology.VectorBundle.Basic

/-!
# Holomorphic scaling and the bar-connection Leibniz rule

Holomorphic functions multiply smooth bundle sections to smooth sections,
and the projected bar derivative of a scaled section is the scalar value
times the bar derivative of the original section. Simpson,
alg-geom/9604005v1, section 2, printed pages 9--11.
-/

@[expose] public noncomputable section

open TopologicalSpace
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.ManifoldDifferentialForms
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
open MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicSectionKernels
open MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
open scoped Manifold ContDiff Topology Matrix Matrix.Norms.Elementwise

open scoped Classical in
/-- Scalar extension of a holomorphic function by zero outside its open. -/
private def scalarExt {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] (U : Opens M)
    (f : HolomorphicScalars (n := n) U) : M → ℂ :=
  fun x => if hx : x ∈ U then f.val ⟨x, hx⟩ else 0

/-- Coordinates of a holomorphically scaled section. -/
private theorem coord_smul_eq {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] {r : ℕ} (B : SmoothComplexBundle n M r)
    (U : Opens M) (f : HolomorphicScalars (n := n) U) (s : RoughSection B U)
    (i : Fin B.count) :
    coordinateSection B i U (f • s)
      = scalarExt U f • coordinateSection B i U s := by
  funext x
  change coordinateSection B i U (f • s) x
    = scalarExt U f x • coordinateSection B i U s x
  rw [scalarExt]
  by_cases hx : x ∈ U
  · simp only [dite_eq_left hx, coordinateSection, holomorphic_smul_apply,
      VectorBundleCore.localTriv_apply]
    change B.core.coordChange (B.core.indexAt x) i x
        (f.val ⟨x, hx⟩ • s ⟨x, hx⟩)
      = f.val ⟨x, hx⟩ • B.core.coordChange (B.core.indexAt x) i x (s ⟨x, hx⟩)
    exact map_smul _ _ _
  · simp only [coordinateSection, dite_eq_right hx, smul_zero]

/-- Complex scalar multiplication on fibres is real-smooth. -/
private instance contMDiffSMul_complex_fiber {r : ℕ} :
    ContMDiffSMul 𝓘(ℝ, ℂ) 𝓘(ℝ, FiberCoordinates r) ∞ ℂ (FiberCoordinates r) where
  contMDiff_smul := by
    have h : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, FiberCoordinates r))
        𝓘(ℝ, ℂ × FiberCoordinates r) ∞ (@id (ℂ × FiberCoordinates r)) := by
      rw [contMDiff_prod_module_iff, ← contMDiff_prod_iff]; exact contMDiff_id
    exact contDiff_smul.contMDiff.comp h

/-- The real chart expression of the scalar extension is the holomorphic chart function. -/
private theorem scalarExt_chart_mem {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] (U : Opens M)
    (f : HolomorphicScalars (n := n) U) (x₀ : M) (y : ℂ) (z : Coordinates n)
    (hz : z ∈ chartDomain ℂ (Coordinates n) M U x₀) :
    ((extChartAt 𝓘(ℝ, ℂ) y) ∘ scalarExt U f ∘ (extChartAt 𝓘(ℝ, Coordinates n) x₀).symm) z
      = chartFunction (Coordinates n) M f.val x₀ z := by
  have hdom : chartDomain ℂ (Coordinates n) M U x₀
      = chartDomain ℝ (Coordinates n) M U x₀ := rfl
  rw [hdom] at hz
  obtain ⟨hzt, hzu⟩ := hz
  change scalarExt U f ((extChartAt 𝓘(ℝ, Coordinates n) x₀).symm z) = _
  have hmem : (extChartAt 𝓘(ℝ, Coordinates n) x₀).symm z ∈ U := hzu
  rw [scalarExt, dite_eq_left hmem]
  rw [chartFunction, dite_eq_left]
  · rfl
  · exact ⟨hzt, hzu⟩

/-- Holomorphic functions extend to real-smooth functions on their open. -/
private theorem contMDiffOn_scalarExt {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] (U : Opens M)
    (f : HolomorphicScalars (n := n) U) :
    ContMDiffOn 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℂ) ∞ (scalarExt U f) ↑U := by
  apply contMDiffOn_of_locally_contMDiffOn
  intro x₀ hx₀
  refine ⟨(extChartAt 𝓘(ℝ, Coordinates n) x₀).source,
    isOpen_extChartAt_source x₀, by simp, ?_⟩
  rw [contMDiffOn_iff_of_subset_source' (x := x₀) (y := scalarExt U f x₀)
    Set.inter_subset_right (fun _ _ => by simp)]
  refine ContDiffOn.mono (ContDiffOn.congr ((f.property x₀).restrict_scalars ℝ)
    (scalarExt_chart_mem U f x₀ (scalarExt U f x₀))) ?_
  intro z hz
  simp only [Set.mem_image] at hz
  obtain ⟨w, hwmem, rfl⟩ := hz
  obtain ⟨hwU, hws⟩ := hwmem
  have hdom : chartDomain ℂ (Coordinates n) M U x₀
    = chartDomain ℝ (Coordinates n) M U x₀ := rfl
  rw [hdom, chartDomain]
  refine ⟨(extChartAt 𝓘(ℝ, Coordinates n) x₀).map_source hws, ?_⟩
  change (extChartAt 𝓘(ℝ, Coordinates n) x₀).symm
    ((extChartAt 𝓘(ℝ, Coordinates n) x₀) w) ∈ (U : Set M)
  rw [(extChartAt 𝓘(ℝ, Coordinates n) x₀).left_inv hws]
  exact hwU

/-- Holomorphic scaling preserves smooth sections. -/
private theorem smooth_smul {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] {r : ℕ} (B : SmoothComplexBundle n M r)
    (U : Opens M) (f : HolomorphicScalars (n := n) U) (s : RoughSection B U)
    (hs : IsSmoothSection B U s) : IsSmoothSection B U (f • s) := by
  intro i
  rw [coord_smul_eq B U f s i]
  exact ContMDiffOn.smul ((contMDiffOn_scalarExt U f).mono Set.inter_subset_left) (hs i)

/-- The chart domain over an open is a neighborhood of the chart point. -/
private theorem chartDomain_mem_nhds {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] (U : Opens M) (x₀ : M) (hx₀ : x₀ ∈ (U : Set M)) :
    chartDomain ℂ (Coordinates n) M U x₀
      ∈ 𝓝 ((extChartAt 𝓘(ℂ, Coordinates n) x₀) x₀) := by
  have h1 : (extChartAt 𝓘(ℂ, Coordinates n) x₀).target
      ∈ 𝓝 ((extChartAt 𝓘(ℂ, Coordinates n) x₀) x₀) :=
    (isOpen_extChartAt_target x₀).mem_nhds (mem_extChartAt_target x₀)
  have hmem : (extChartAt 𝓘(ℂ, Coordinates n) x₀).symm
      ((extChartAt 𝓘(ℂ, Coordinates n) x₀) x₀) ∈ (U : Set M) := by
    rw [(extChartAt 𝓘(ℂ, Coordinates n) x₀).left_inv (mem_extChartAt_source x₀)]
    exact hx₀
  have h2 : (extChartAt 𝓘(ℂ, Coordinates n) x₀).symm ⁻¹' (U : Set M)
      ∈ 𝓝 ((extChartAt 𝓘(ℂ, Coordinates n) x₀) x₀) :=
    (continuousAt_extChartAt_symm'' (mem_extChartAt_target x₀)).preimage_mem_nhds
      (U.2.mem_nhds hmem)
  exact Filter.inter_mem h1 h2

/-- The real derivative of a holomorphic extension is complex-linear. -/
private theorem scalarExt_complex_linear {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] {r : ℕ} (B : SmoothComplexBundle n M r)
    (U : Opens M) (f : HolomorphicScalars (n := n) U) (i : Fin B.count) {x₀ : M}
    (hx₀ : x₀ ∈ (U : Set M)) (hxbase : x₀ ∈ B.core.baseSet i) (v : Coordinates n) :
    (show ℂ from mfderivWithin 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℂ) (scalarExt U f)
      (↑U ∩ B.core.baseSet i) x₀ (Complex.I • v))
      = Complex.I • (show ℂ from mfderivWithin 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℂ)
        (scalarExt U f) (↑U ∩ B.core.baseSet i) x₀ v) := by
  have hpt : (extChartAt 𝓘(ℝ, Coordinates n) x₀) x₀
      = (extChartAt 𝓘(ℂ, Coordinates n) x₀) x₀ := rfl
  have hS_nhds : chartDomain ℂ (Coordinates n) M U x₀
      ∈ 𝓝 ((extChartAt 𝓘(ℝ, Coordinates n) x₀) x₀) := by
    rw [hpt]
    exact chartDomain_mem_nhds U x₀ hx₀
  have hChart : HasFDerivAt (chartFunction (Coordinates n) M f.val x₀)
      (fderiv ℂ (chartFunction (Coordinates n) M f.val x₀)
        ((extChartAt 𝓘(ℝ, Coordinates n) x₀) x₀))
      ((extChartAt 𝓘(ℝ, Coordinates n) x₀) x₀) :=
    (((f.property x₀).contDiffAt hS_nhds).differentiableAt (by simp)).hasFDerivAt
  have hChartR := hChart.restrictScalars ℝ
  have hAgree : ∀ z ∈ chartDomain ℂ (Coordinates n) M U x₀,
      (scalarExt U f ∘ (extChartAt 𝓘(ℝ, Coordinates n) x₀).symm) z
        = chartFunction (Coordinates n) M f.val x₀ z := by
    intro z hz
    have hdom : chartDomain ℂ (Coordinates n) M U x₀
        = chartDomain ℝ (Coordinates n) M U x₀ := rfl
    rw [hdom] at hz
    obtain ⟨hzt, hzu⟩ := hz
    change scalarExt U f ((extChartAt 𝓘(ℝ, Coordinates n) x₀).symm z) = _
    have hmem : (extChartAt 𝓘(ℝ, Coordinates n) x₀).symm z ∈ U := hzu
    rw [scalarExt, dite_eq_left hmem, chartFunction, dite_eq_left]
    · rfl
    · exact ⟨hzt, hzu⟩
  have hz₀S : (extChartAt 𝓘(ℝ, Coordinates n) x₀) x₀
      ∈ chartDomain ℂ (Coordinates n) M U x₀ := by
    have hdom : chartDomain ℂ (Coordinates n) M U x₀
        = chartDomain ℝ (Coordinates n) M U x₀ := rfl
    rw [hdom, chartDomain]
    refine ⟨mem_extChartAt_target x₀, ?_⟩
    change (extChartAt 𝓘(ℝ, Coordinates n) x₀).symm
      ((extChartAt 𝓘(ℝ, Coordinates n) x₀) x₀) ∈ (U : Set M)
    rw [(extChartAt 𝓘(ℝ, Coordinates n) x₀).left_inv (mem_extChartAt_source x₀)]
    exact hx₀
  have hWithin : HasFDerivWithinAt
      (scalarExt U f ∘ (extChartAt 𝓘(ℝ, Coordinates n) x₀).symm)
      ((fderiv ℂ (chartFunction (Coordinates n) M f.val x₀)
        ((extChartAt 𝓘(ℝ, Coordinates n) x₀) x₀)).restrictScalars ℝ)
      ((extChartAt 𝓘(ℝ, Coordinates n) x₀).symm ⁻¹' (↑U ∩ B.core.baseSet i)
        ∩ Set.range 𝓘(ℝ, Coordinates n))
      ((extChartAt 𝓘(ℝ, Coordinates n) x₀) x₀) := by
    apply HasFDerivWithinAt.congr_of_eventuallyEq hChartR.hasFDerivWithinAt _ _
    · apply Filter.eventuallyEq_of_mem (mem_nhdsWithin_of_mem_nhds hS_nhds)
      intro z hz
      exact hAgree z hz
    · exact hAgree _ hz₀S
  have hCont : ContinuousWithinAt (scalarExt U f) (↑U ∩ B.core.baseSet i) x₀ :=
    ((contMDiffOn_scalarExt U f).continuousOn.mono
      Set.inter_subset_left).continuousWithinAt ⟨hx₀, hxbase⟩
  have hMF : HasMFDerivWithinAt 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℂ) (scalarExt U f)
      (↑U ∩ B.core.baseSet i) x₀
      ((tangentSpaceCastModel 𝓘(ℝ, ℂ) (scalarExt U f x₀)).symm.toContinuousLinearMap ∘L
        (fderiv ℂ (chartFunction (Coordinates n) M f.val x₀)
          ((extChartAt 𝓘(ℝ, Coordinates n) x₀) x₀)).restrictScalars ℝ ∘L
        (tangentSpaceCastModel 𝓘(ℝ, Coordinates n) x₀).toContinuousLinearMap) := by
    refine ⟨hCont, ?_⟩
    change HasFDerivWithinAt (scalarExt U f ∘ (extChartAt 𝓘(ℝ, Coordinates n) x₀).symm)
      ((fderiv ℂ (chartFunction (Coordinates n) M f.val x₀)
        ((extChartAt 𝓘(ℝ, Coordinates n) x₀) x₀)).restrictScalars ℝ)
      ((extChartAt 𝓘(ℝ, Coordinates n) x₀).symm ⁻¹' (↑U ∩ B.core.baseSet i)
        ∩ Set.range 𝓘(ℝ, Coordinates n))
      ((extChartAt 𝓘(ℝ, Coordinates n) x₀) x₀)
    exact hWithin
  have hU : UniqueMDiffWithinAt 𝓘(ℝ, Coordinates n) (↑U ∩ B.core.baseSet i) x₀ :=
    (U.2.inter (B.core.isOpen_baseSet i)).uniqueMDiffWithinAt ⟨hx₀, hxbase⟩
  have hEq := hMF.mfderivWithin hU
  rw [hEq]
  change ((fderiv ℂ (chartFunction (Coordinates n) M f.val x₀)
      ((extChartAt 𝓘(ℝ, Coordinates n) x₀) x₀)).restrictScalars ℝ) (Complex.I • v)
    = Complex.I • ((fderiv ℂ (chartFunction (Coordinates n) M f.val x₀)
      ((extChartAt 𝓘(ℝ, Coordinates n) x₀) x₀)).restrictScalars ℝ) v
  exact (fderiv ℂ (chartFunction (Coordinates n) M f.val x₀)
    ((extChartAt 𝓘(ℝ, Coordinates n) x₀) x₀)).map_smul _ _

/-- Leibniz rule for `mvfderivWithin` of a complex-scaled vector function. -/
private theorem mvfderivWithin_smul_complex {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] {r : ℕ} {F₀ : M → ℂ}
    {G : M → FiberCoordinates r} {T : Set M} {x₀ : M}
    (hF : MDifferentiableWithinAt 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℂ) F₀ T x₀)
    (hG : MDifferentiableWithinAt 𝓘(ℝ, Coordinates n) 𝓘(ℝ, FiberCoordinates r) G T x₀)
    (hs : UniqueMDiffWithinAt 𝓘(ℝ, Coordinates n) T x₀) :
    mvfderivWithin 𝓘(ℝ, Coordinates n) (F₀ • G) T x₀
      = F₀ x₀ • mvfderivWithin 𝓘(ℝ, Coordinates n) G T x₀
        + (mvfderivWithin 𝓘(ℝ, Coordinates n) F₀ T x₀).smulRight (G x₀) := by
  refine HasMFDerivWithinAt.mfderivWithin ⟨hF.1.smul hG.1, ?_⟩ hs
  convert! hF.hasMFDerivWithinAt.2.smul hG.hasMFDerivWithinAt.2
  simp
  rfl

/-- Applied Leibniz rule for `mfderivWithin` of a complex-scaled vector function. -/
private theorem mfderivWithin_smul_apply {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] {r : ℕ} {F₀ : M → ℂ}
    {G : M → FiberCoordinates r} {T : Set M} {x₀ : M}
    (hF : MDifferentiableWithinAt 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℂ) F₀ T x₀)
    (hG : MDifferentiableWithinAt 𝓘(ℝ, Coordinates n) 𝓘(ℝ, FiberCoordinates r) G T x₀)
    (hs : UniqueMDiffWithinAt 𝓘(ℝ, Coordinates n) T x₀)
    (v : Coordinates n) :
    (show FiberCoordinates r from mfderivWithin 𝓘(ℝ, Coordinates n)
      𝓘(ℝ, FiberCoordinates r) (F₀ • G) T x₀ v)
      = F₀ x₀ • (show FiberCoordinates r from mfderivWithin 𝓘(ℝ, Coordinates n)
          𝓘(ℝ, FiberCoordinates r) G T x₀ v)
        + (show ℂ from mfderivWithin 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℂ) F₀ T x₀ v) • G x₀ := by
  have h := congrArg (fun L : TangentSpace 𝓘(ℝ, Coordinates n) x₀ →L[ℝ] FiberCoordinates r => L v)
    (mvfderivWithin_smul_complex hF hG hs)
  exact h

/-- Module identity for the bar Leibniz rule under a vanishing scalar hypothesis. -/
private theorem bar_algebra {r : ℕ} (F : ℂ) (D3 D4 Gx Mx : FiberCoordinates r)
    (dFu dFIu : ℂ) (h : (1 / 2 : ℂ) • (dFu + Complex.I • dFIu) = 0) :
    (1 / 2 : ℂ) • ((F • D3 + dFu • Gx) + Complex.I • (F • D4 + dFIu • Gx)) + F • Mx
      = F • ((1 / 2 : ℂ) • (D3 + Complex.I • D4) + Mx) := by
  have key : (1 / 2 : ℂ) • ((F • D3 + dFu • Gx) + Complex.I • (F • D4 + dFIu • Gx))
      + F • Mx
      = F • ((1 / 2 : ℂ) • (D3 + Complex.I • D4) + Mx)
        + ((1 / 2 : ℂ) • (dFu + Complex.I • dFIu)) • Gx := by
    module
  rw [key, h, zero_smul, add_zero]

/-- Holomorphic scaling satisfies the bar-derivative Leibniz rule. -/
private theorem bar_smul {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] {r : ℕ} (B : SmoothComplexBundle n M r)
    (h : HermitianMetric B) (A : SmoothConnection B) (U : Opens M)
    (f : HolomorphicScalars (n := n) U) (s : RoughSection B U)
    (hs : IsSmoothSection B U s) (i : Fin B.count) (x : U)
    (hx : x.val ∈ B.core.baseSet i) (u : Coordinates n) :
    barConnectionValue B h A i U (f • s) x u
      = f.val x • barConnectionValue B h A i U s x u := by
  have hxU : x.val ∈ U := x.property
  have hFx : scalarExt U f x.val = f.val x := by
    rw [scalarExt, dite_eq_left hxU]
  have hU : UniqueMDiffWithinAt 𝓘(ℝ, Coordinates n) (↑U ∩ B.core.baseSet i) x.val :=
    (U.2.inter (B.core.isOpen_baseSet i)).uniqueMDiffWithinAt ⟨x.property, hx⟩
  have hF_diff : MDifferentiableWithinAt 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℂ) (scalarExt U f)
      (↑U ∩ B.core.baseSet i) x.val :=
    ((contMDiffOn_scalarExt U f).mono Set.inter_subset_left).mdifferentiableOn (by simp)
      x.val ⟨x.property, hx⟩
  have hG_diff : MDifferentiableWithinAt 𝓘(ℝ, Coordinates n) 𝓘(ℝ, FiberCoordinates r)
      (coordinateSection B i U s) (↑U ∩ B.core.baseSet i) x.val :=
    (hs i).mdifferentiableOn (by simp) x.val ⟨x.property, hx⟩
  have hLu := mfderivWithin_smul_apply hF_diff hG_diff hU u
  have hLIu := mfderivWithin_smul_apply hF_diff hG_diff hU (Complex.I • u)
  have hCL := scalarExt_complex_linear B U f i x.property hx u
  have hCR : (1 / 2 : ℂ) • ((show ℂ from mfderivWithin 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℂ)
      (scalarExt U f) (↑U ∩ B.core.baseSet i) x.val u)
      + Complex.I • (show ℂ from mfderivWithin 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℂ)
        (scalarExt U f) (↑U ∩ B.core.baseSet i) x.val (Complex.I • u))) = 0 := by
    rw [hCL]
    generalize (show ℂ from mfderivWithin 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℂ)
      (scalarExt U f) (↑U ∩ B.core.baseSet i) x.val u) = a
    simp only [smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
    ring
  simp only [barConnectionValue_formula]
  rw [coord_smul_eq B U f s i]
  have hPG : (scalarExt U f • coordinateSection B i U s) x.val
      = f.val x • coordinateSection B i U s x.val := by
    change scalarExt U f x.val • coordinateSection B i U s x.val = _
    rw [hFx]
  simp only [hLu, hLIu, hPG, hFx, Matrix.mulVec_smul]
  exact bar_algebra (f.val x)
    (show FiberCoordinates r from mfderivWithin 𝓘(ℝ, Coordinates n)
      𝓘(ℝ, FiberCoordinates r) (coordinateSection B i U s)
      (↑U ∩ B.core.baseSet i) x.val u)
    (show FiberCoordinates r from mfderivWithin 𝓘(ℝ, Coordinates n)
      𝓘(ℝ, FiberCoordinates r) (coordinateSection B i U s)
      (↑U ∩ B.core.baseSet i) x.val (Complex.I • u))
    (coordinateSection B i U s x.val)
    (extractedBarConnection B h A i x.val u *ᵥ coordinateSection B i U s x.val)
    (show ℂ from mfderivWithin 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℂ)
      (scalarExt U f) (↑U ∩ B.core.baseSet i) x.val u)
    (show ℂ from mfderivWithin 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℂ)
      (scalarExt U f) (↑U ∩ B.core.baseSet i) x.val (Complex.I • u))
    hCR

/-- Holomorphic multiplication satisfies the actual full bar-derivative Leibniz rule. -/
theorem holomorphic_bar_multiplication {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] {r : ℕ}
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    (B : SmoothComplexBundle n M r)
    (h : HermitianMetric B) (A : SmoothConnection B) : BarMultiplicationCalculus B h A :=
  ⟨smooth_smul B, bar_smul B h A⟩
