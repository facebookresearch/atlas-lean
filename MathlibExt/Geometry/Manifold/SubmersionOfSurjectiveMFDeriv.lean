/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module


public import Mathlib.Geometry.Manifold.Submersion
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

import Mathlib.Algebra.Module.Projective
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Submersions from surjective manifold derivatives

This file proves that a map from a Banach manifold to a finite-dimensional manifold over `ℝ` or
`ℂ` is a submersion at a point when it is smooth on a neighbourhood and its manifold derivative
there is surjective, and derives the finite-dimensional criterion.
-/

@[expose] public section

open scoped Topology ContDiff
open Manifold

noncomputable section

private theorem submersionSurj_split
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (A : E →L[𝕜] F) (hA : Function.Surjective A) :
    ∃ e : E ≃L[𝕜] F × LinearMap.ker (A : E →ₗ[𝕜] F), ∀ z, (e z).1 = A z := by
  obtain ⟨Rlin, hRlin⟩ := LinearMap.exists_rightInverse_of_surjective
    (f := (A : E →ₗ[𝕜] F)) (LinearMap.range_eq_top.mpr hA)
  let R : F →L[𝕜] E := Rlin.toContinuousLinearMap
  have hR : Function.RightInverse R A := by
    intro y
    have h := congrArg (fun g : F →ₗ[𝕜] F ↦ g y) hRlin
    simpa [R] using h
  let e := ContinuousLinearEquiv.equivOfRightInverse A R hR
  exact ⟨e, fun z ↦ ContinuousLinearEquiv.fst_equivOfRightInverse A R hR z⟩

private theorem submersionSurj_eventually_contDiffAt_writtenInExtChartAt
    {𝕜 E E'' H G M N : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G}
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [I.Boundaryless] [IsManifold I n M] [IsManifold J n N]
    {f : M → N} {x : M} (hfn : ∀ᶠ y in 𝓝 x, ContMDiffAt I J n f y) :
    ∀ᶠ z in 𝓝 (extChartAt I x x),
      ContDiffAt 𝕜 n (writtenInExtChartAt I J x f) z := by
  have hfx : ContMDiffAt I J n f x := hfn.self_of_nhds
  have hxSource : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  have hfxSource : f ⁻¹' (chartAt G (f x)).source ∈ 𝓝 x :=
    hfx.continuousAt <| (chartAt G (f x)).open_source.mem_nhds (mem_chart_source G (f x))
  have hyGood : ∀ᶠ y in 𝓝 x,
      ContMDiffAt I J n f y ∧ y ∈ (chartAt H x).source ∧
        f y ∈ (chartAt G (f x)).source := by
    filter_upwards [hfn, hxSource, hfxSource] with y hfy hySource hfySource
    exact ⟨hfy, hySource, hfySource⟩
  have hyGood' : ∀ᶠ y in 𝓝 ((extChartAt I x).symm (extChartAt I x x)),
      ContMDiffAt I J n f y ∧ y ∈ (chartAt H x).source ∧
        f y ∈ (chartAt G (f x)).source := by
    simpa only [extChartAt_to_inv] using hyGood
  have hzGood := (continuousAt_extChartAt_symm x) hyGood'
  filter_upwards [extChartAt_target_mem_nhds x, hzGood] with z hz hgood
  rcases hgood with ⟨hfz, hzSource, hfzSource⟩
  have hcharts := ((contMDiffAt_iff_of_mem_source hzSource hfzSource).mp hfz).2
  rw [(extChartAt I x).right_inv hz] at hcharts
  rw [I.range_eq_univ, contDiffWithinAt_univ] at hcharts
  simpa [writtenInExtChartAt] using hcharts

private theorem submersionSurj_eventually_isInvertible_fderiv
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : ℕ∞ω} {f : E → F} {a : E} (hn : n ≠ 0)
    (hf : ContDiffAt 𝕜 n f a) (f' : E ≃L[𝕜] F)
    (hf' : HasFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ z in 𝓝 a, (fderiv 𝕜 f z).IsInvertible := by
  have ha : (fderiv 𝕜 f a).IsInvertible := by
    rw [hf'.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv
  exact hf.continuousAt_fderiv hn ha.eventually_nhds

private theorem submersionSurj_partialDiffeomorph_of_hasFDerivAt_equiv
    {𝕜 : Type*} [RCLike 𝕜] {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : ℕ∞ω} {f : E → F} {a : E}
    (hfn : ∀ᶠ z in 𝓝 a, ContDiffAt 𝕜 n f z) (f' : E ≃L[𝕜] F)
    (hf' : HasFDerivAt f (f' : E →L[𝕜] F) a) (hn : n ≠ 0) :
    ∃ Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) E F n,
      a ∈ Φ.source ∧ Set.EqOn f Φ Φ.source := by
  have hf : ContDiffAt 𝕜 n f a := hfn.self_of_nhds
  let e₀ := hf.toOpenPartialHomeomorph f hf' hn
  have he₀ : (e₀ : E → F) = f := hf.toOpenPartialHomeomorph_coe hf' hn
  have ha : a ∈ e₀.source := hf.mem_toOpenPartialHomeomorph_source hf' hn
  have hInv := submersionSurj_eventually_isInvertible_fderiv hn hf f' hf'
  have hgood : ∀ᶠ z in 𝓝 a,
      ContDiffAt 𝕜 n f z ∧ (fderiv 𝕜 f z).IsInvertible := hfn.and hInv
  obtain ⟨U, hU, hUopen, haU⟩ := eventually_nhds_iff.mp hgood
  let e := e₀.restrOpen U hUopen
  have hae : a ∈ e.source := by
    simpa only [e, OpenPartialHomeomorph.restrOpen_source] using ⟨ha, haU⟩
  have he_contDiff : ContDiffOn 𝕜 n e e.source := by
    intro z hz
    have hzU : z ∈ U := by
      simpa only [e, OpenPartialHomeomorph.restrOpen_source] using hz.2
    rw [OpenPartialHomeomorph.coe_restrOpen, he₀]
    exact (hU z hzU).1.contDiffWithinAt
  have he_symm_contDiff : ContDiffOn 𝕜 n e.symm e.target := by
    intro y hy
    have hzs : e.symm y ∈ e.source := e.map_target hy
    have hzU : e.symm y ∈ U := by
      simpa only [e, OpenPartialHomeomorph.restrOpen_source] using hzs.2
    obtain ⟨e', he'⟩ := (hU (e.symm y) hzU).2
    have hderiv : HasFDerivAt f (e' : E →L[𝕜] F) (e.symm y) := by
      rw [he']
      exact ((hU (e.symm y) hzU).1.differentiableAt hn).hasFDerivAt
    have hderiv_e : HasFDerivAt e (e' : E →L[𝕜] F) (e.symm y) := by
      rw [OpenPartialHomeomorph.coe_restrOpen, he₀]
      exact hderiv
    have he_at : ContDiffAt 𝕜 n e (e.symm y) := by
      rw [OpenPartialHomeomorph.coe_restrOpen, he₀]
      exact (hU (e.symm y) hzU).1
    exact (e.contDiffAt_symm hy hderiv_e he_at).contDiffWithinAt
  let Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) E F n := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := he_contDiff.contMDiffOn
    contMDiffOn_invFun := he_symm_contDiff.contMDiffOn
  }
  refine ⟨Φ, hae, ?_⟩
  intro z hz
  change f z = e z
  rw [OpenPartialHomeomorph.coe_restrOpen, he₀]

private theorem submersionSurj_localNormalForm
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {n : ℕ∞ω} {g : E → F} {a : E} (hn : n ≠ 0)
    (hgn : ∀ᶠ z in 𝓝 a, ContDiffAt 𝕜 n g z)
    (A : E →L[𝕜] F) (hg' : HasFDerivAt g A a) (hA : Function.Surjective A) :
    ∃ (e : E ≃L[𝕜] F × LinearMap.ker (A : E →ₗ[𝕜] F))
      (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) E E n),
      a ∈ Φ.source ∧ Set.EqOn (g ∘ Φ.symm) (Prod.fst ∘ e) Φ.target := by
  obtain ⟨e, he⟩ := submersionSurj_split A hA
  let B : E →L[𝕜] LinearMap.ker (A : E →ₗ[𝕜] F) :=
    (ContinuousLinearMap.snd 𝕜 F _).comp e.toContinuousLinearMap
  let q : E → E := fun z ↦ e.symm (g z, B z)
  have hB : HasFDerivAt (fun z ↦ B z) B a := B.hasFDerivAt
  have hq' : HasFDerivAt q (ContinuousLinearMap.id 𝕜 E) a := by
    have hcomp := e.symm.hasFDerivAt.comp a (hg'.prodMk hB)
    have hlin : e.symm.toContinuousLinearMap.comp (A.prod B) =
        ContinuousLinearMap.id 𝕜 E := by
      ext z
      change e.symm (A z, B z) = z
      apply e.injective
      rw [e.apply_symm_apply]
      ext
      · simpa using (he z).symm
      · simp [B]
    change HasFDerivAt (e.symm ∘ fun z ↦ (g z, B z)) (ContinuousLinearMap.id 𝕜 E) a
    simpa only [hlin] using hcomp
  have hqn : ∀ᶠ z in 𝓝 a, ContDiffAt 𝕜 n q z := by
    filter_upwards [hgn] with z hgz
    dsimp only [q]
    fun_prop
  obtain ⟨Φ, haΦ, hqΦ⟩ :=
    submersionSurj_partialDiffeomorph_of_hasFDerivAt_equiv
      hqn (ContinuousLinearEquiv.refl 𝕜 E) hq' hn
  refine ⟨e, Φ, haΦ, ?_⟩
  intro z hz
  have hzs : Φ.symm z ∈ Φ.source := Φ.map_target hz
  have hqeq := hqΦ hzs
  have hright := Φ.right_inv hz
  change g (Φ.symm z) = (e z).1
  calc
    g (Φ.symm z) = (e (q (Φ.symm z))).1 := by simp [q]
    _ = (e (Φ (Φ.symm z))).1 := congrArg (fun w ↦ (e w).1) hqeq
    _ = (e z).1 := congrArg (fun w ↦ (e w).1) hright

private def submersionSurj_modelPartialDiffeomorph
    {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] (n : ℕ∞ω) :
    PartialDiffeomorph I 𝓘(𝕜, E) H E n where
  toPartialEquiv := I.toHomeomorph.toPartialEquiv
  open_source := by simp
  open_target := by simp
  contMDiffOn_toFun := I.contMDiff.contMDiffOn
  contMDiffOn_invFun := by
    simpa [ModelWithCorners.toHomeomorph, I.range_eq_univ] using
      (I.contMDiffOn_symm (n := n))

private theorem submersionSurj_mk_of_localNormalForm
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E E'' K H G : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G}
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [I.Boundaryless] [IsManifold I n M] [IsManifold J n N]
    {f : M → N} {x : M} (hf : ContinuousAt f x)
    (e : E ≃L[𝕜] E'' × K)
    (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) E E n)
    (hxΦ : extChartAt I x x ∈ Φ.source)
    (hnormal : Set.EqOn (writtenInExtChartAt I J x f ∘ Φ.symm)
      (Prod.fst ∘ e) Φ.target) :
    IsSubmersionAt I J n f x := by
  let IΦ : PartialDiffeomorph I I H H n :=
    (submersionSurj_modelPartialDiffeomorph I n).trans
      (Φ.trans (submersionSurj_modelPartialDiffeomorph I n).symm)
  let domChart : OpenPartialHomeomorph M H :=
    (chartAt H x).trans IΦ.toOpenPartialHomeomorph
  have hIΦcoe : (IΦ.toOpenPartialHomeomorph : H → H) = IΦ := by
    funext y
    rfl
  have hIΦsymmcoe : (IΦ.toOpenPartialHomeomorph.symm : H → H) = IΦ.symm := by
    funext y
    rfl
  have hxdom : x ∈ domChart.source := by
    simpa only [domChart, IΦ, submersionSurj_modelPartialDiffeomorph,
      OpenPartialHomeomorph.trans_toPartialEquiv,
      PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv,
      PartialDiffeomorph.trans_toPartialEquiv, PartialDiffeomorph.symm_toPartialEquiv,
      PartialEquiv.trans_source, PartialHomeomorph.toFun_eq_coe,
      OpenPartialHomeomorph.coe_toPartialHomeomorph, Equiv.toPartialEquiv_source,
      Equiv.toPartialEquiv_apply, Homeomorph.coe_toEquiv, PartialEquiv.symm_source,
      Equiv.toPartialEquiv_target, Set.preimage_univ, Set.inter_univ, Set.univ_inter,
      Set.mem_inter_iff, mem_chart_source, Set.mem_preimage,
      ModelWithCorners.toHomeomorph_apply, true_and, extChartAt,
      OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
      ModelWithCorners.toPartialEquiv_coe, Function.comp_apply] using hxΦ
  have hdom : domChart ∈ IsManifold.maximalAtlas I n M := by
    apply domChart.mem_maximalAtlas_of_contMDiffOn
    · simpa [domChart, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.coe_trans,
        PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv,
        hIΦcoe] using
        IΦ.contMDiffOn.comp
          (contMDiffOn_chart.mono Set.inter_subset_left) Set.inter_subset_right
    · simpa [domChart, OpenPartialHomeomorph.trans_target,
        OpenPartialHomeomorph.coe_trans_symm,
        PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv,
        hIΦsymmcoe] using
        (contMDiffOn_chart_symm (I := I) (x := x)).comp
          (IΦ.symm.contMDiffOn.mono Set.inter_subset_left) Set.inter_subset_right
  apply IsSubmersionAt.mk_of_continuousAt hf e domChart (chartAt G (f x))
  · exact hxdom
  · exact mem_chart_source G (f x)
  · exact hdom
  · exact IsManifold.chart_mem_maximalAtlas (f x)
  · intro z hz
    simp only [OpenPartialHomeomorph.extend, submersionSurj_modelPartialDiffeomorph,
      OpenPartialHomeomorph.trans_toPartialEquiv,
      PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv,
      PartialDiffeomorph.trans_toPartialEquiv, PartialDiffeomorph.symm_toPartialEquiv,
      PartialEquiv.trans_target, ModelWithCorners.target_eq,
      ModelWithCorners.toPartialEquiv_coe_symm, PartialEquiv.symm_target,
      Equiv.toPartialEquiv_source, PartialEquiv.symm_symm, Equiv.toPartialEquiv_apply,
      Homeomorph.coe_toEquiv, Set.univ_inter, PartialEquiv.coe_trans_symm,
      Equiv.toPartialEquiv_target, Set.preimage_univ, Set.inter_univ,
      Equiv.toPartialEquiv_symm_apply, Homeomorph.coe_symm_toEquiv, Set.preimage_inter,
      Set.mem_inter_iff, Set.mem_range, Set.mem_preimage, ModelWithCorners.toHomeomorph_apply,
      Function.comp_apply, ModelWithCorners.toHomeomorph_symm_apply, PartialEquiv.coe_trans,
      ModelWithCorners.toPartialEquiv_coe, PartialHomeomorph.toFun_eq_coe,
      OpenPartialHomeomorph.coe_toPartialHomeomorph,
      PartialHomeomorph.coe_toPartialEquiv_symm,
      OpenPartialHomeomorph.coe_toPartialHomeomorph_symm, domChart, IΦ] at hz ⊢
    have hIz : I (I.symm z) = z := I.toHomeomorph.apply_symm_apply z
    rw [hIz] at hz ⊢
    simpa [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend,
      Function.comp_apply] using hnormal hz.2.1

namespace Manifold.IsSubmersionAt

universe u

/-- **Surjective differential into a finite-dimensional manifold gives a submersion.** Let
$\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $n \in \mathbb{N} \cup \{\infty, \omega\}$ with
$n \ge 1$, let $M$ be a $C^n$ manifold without boundary over $\mathbb{K}$ modelled on a Banach
space, and let $N$ be a $C^n$ manifold, possibly with boundary or corners, over $\mathbb{K}$
modelled on a finite-dimensional space. If $f : M \to N$ is $C^n$ at every point of some
neighbourhood of $x \in M$ and the manifold derivative of $f$ at $x$ is surjective, then $f$ is a
$C^n$ submersion at $x$: there are charts of the $C^n$ maximal atlases around $x$ and $f(x)$, the
first mapped by $f$ into the second, in which $f$ reads $(u, v) \mapsto u$ after a continuous linear
identification of the model space of $M$ with the product of the model space of $N$ and some
normed space. -/
theorem of_surjective_mfderiv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    {E : Type u} {E'' H G M N : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [FiniteDimensional 𝕜 E'']
    [TopologicalSpace H] [TopologicalSpace G]
    {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G}
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [I.Boundaryless] [IsManifold I n M] [IsManifold J n N]
    {f : M → N} {x : M} (hn : 1 ≤ n)
    (hfn : ∀ᶠ y in 𝓝 x, ContMDiffAt I J n f y)
    (hderiv : Function.Surjective (mfderiv I J f x)) :
    IsSubmersionAt I J n f x := by
  let _ := IsRCLikeNormedField.rclike 𝕜
  let g : E → E'' := writtenInExtChartAt I J x f
  let a : E := extChartAt I x x
  let A : E →L[𝕜] E'' :=
    (tangentSpaceCastModel J (f x)) ∘L mfderiv I J f x ∘L
      (tangentSpaceCastModel I x).symm
  have hn0 : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.mp hn
  have hfx : ContMDiffAt I J n f x := hfn.self_of_nhds
  have hgn : ∀ᶠ z in 𝓝 a, ContDiffAt 𝕜 n g z := by
    simpa [g, a] using submersionSurj_eventually_contDiffAt_writtenInExtChartAt hfn
  have hmd : MDifferentiableAt I J f x := hfx.mdifferentiableAt hn0
  have hg' : HasFDerivAt g A a := by
    have hcharts := hmd.hasMFDerivAt.2
    simpa [g, a, A, I.range_eq_univ] using hcharts
  have hA : Function.Surjective A := by
    intro y
    obtain ⟨v, hv⟩ := hderiv ((tangentSpaceCastModel J (f x)).symm y)
    refine ⟨tangentSpaceCastModel I x v, ?_⟩
    simp [A, hv]
  obtain ⟨e, Φ, haΦ, hnormal⟩ :=
    submersionSurj_localNormalForm hn0 hgn A hg' hA
  exact submersionSurj_mk_of_localNormalForm hfx.continuousAt e Φ haΦ hnormal

end Manifold.IsSubmersionAt

namespace MathlibExt.Geometry.Manifold.SubmersionOfSurjectiveMFDerivWanted

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u} {E'' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G}
variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
variable {n : ℕ∞ω}

/--
**Surjective differential gives a submersion between finite-dimensional manifolds.** Let
$\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $n \in \mathbb{N} \cup \{\infty, \omega\}$ with
$n \ge 1$, and let $M$ and $N$ be $C^n$ manifolds without boundary over $\mathbb{K}$ modelled on
finite-dimensional spaces. If $f : M \to N$ is $C^n$ at every point of some neighbourhood of
$x \in M$ and the manifold derivative of $f$ at $x$ is surjective, then $f$ is a $C^n$ submersion
at $x$: there are charts of the $C^n$ maximal atlases around $x$ and $f(x)$, the first mapped by
$f$ into the second, in which $f$ reads $(u, v) \mapsto u$ after a linear identification of the
model space of $M$ with the product of the model space of $N$ and some normed space.

Proves `Wanted` entry `submersionAt_of_surjective_mfderiv`.

Proof: Split the surjective derivative, augment the map by its kernel coordinate, and apply the
inverse function theorem to obtain charts in which the map is the first projection.

Sources: Mathlib `Mathlib/Geometry/Manifold/Submersion.lean` TODO (finite-dimensional
surjective-`mfderiv` criterion); J. Lee, Introduction to Smooth Manifolds, 2nd ed., Ch. 4.
-/
theorem submersionAt_of_surjective_mfderiv
    [CompleteSpace 𝕜] [IsRCLikeNormedField 𝕜]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'']
    [I.Boundaryless] [J.Boundaryless]
    [IsManifold I n M] [IsManifold J n N]
    {f : M → N} {x : M}
    (hn : 1 ≤ n) (hfn : ∀ᶠ y in 𝓝 x, ContMDiffAt I J n f y)
    (hderiv : Function.Surjective (mfderiv I J f x)) :
    IsSubmersionAt I J n f x := by
  let _ : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  exact Manifold.IsSubmersionAt.of_surjective_mfderiv hn hfn hderiv

end MathlibExt.Geometry.Manifold.SubmersionOfSurjectiveMFDerivWanted
