/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.Notation
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.RingTheory.PicardGroup

@[expose] public section

/-!
# Complex rigidity, open mapping theorem

Nonconstant holomorphic maps between Riemann surfaces are open maps.
-/

open Set Manifold
open scoped Manifold
open Topology Filter

namespace MDifferentiable

/-- A finite-dimensional complex normed space of complex dimension one is
continuously linearly equivalent to `ℂ`. -/
private noncomputable def linEquivFinrankOne (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (h : Module.finrank ℂ E = 1) : E ≃L[ℂ] ℂ :=
  ContinuousLinearEquiv.ofFinrankEq (h.trans (Module.finrank_self ℂ).symm)

/-- Chart package: an `MDiff` map between one-dimensional complex manifolds,
read in fixed extended charts at `x₀` and `f x₀` and conjugated by linear
identifications of the models with `ℂ`, is analytic on an open neighbourhood
in `ℂ`. The filter identities say the chart parametrizations are local
homeomorphisms. -/
private theorem chartPackage
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℂ F G} [J.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    (hE : Module.finrank ℂ E = 1) (hF : Module.finrank ℂ F = 1)
    {f : M → N} (hf : MDiff f) (x₀ : M) :
    ∃ (eE : E ≃L[ℂ] ℂ) (eF : F ≃L[ℂ] ℂ) (V : Set ℂ) (h : ℂ → ℂ),
      IsOpen V ∧
      eE ((extChartAt I x₀) x₀) ∈ V ∧
      AnalyticOnNhd ℂ h V ∧
      h (eE ((extChartAt I x₀) x₀)) = eF ((extChartAt J (f x₀)) (f x₀)) ∧
      (∀ z ∈ V,
        eE.symm z ∈ (extChartAt I x₀).target ∧
        f ((extChartAt I x₀).symm (eE.symm z)) ∈ (extChartAt J (f x₀)).source ∧
        h z = eF ((extChartAt J (f x₀))
          (f ((extChartAt I x₀).symm (eE.symm z))))) ∧
      Filter.map ((extChartAt I x₀).symm ∘ ⇑eE.symm)
          (𝓝 (eE ((extChartAt I x₀) x₀))) = 𝓝 x₀ ∧
      Filter.map ((extChartAt J (f x₀)).symm ∘ ⇑eF.symm)
          (𝓝 (h (eE ((extChartAt I x₀) x₀)))) = 𝓝 (f x₀) := by
  set e := extChartAt I x₀ with he
  set e' := extChartAt J (f x₀) with he'
  set eE := linEquivFinrankOne E hE with heE
  set eF := linEquivFinrankOne F hF with heF
  set p₀ : E := e x₀ with hp₀
  set q₀ : F := e' (f x₀) with hq₀
  set r₀ : ℂ := eE p₀ with hr₀
  set w : E → F := ⇑e' ∘ f ∘ ⇑e.symm with hw
  set h : ℂ → ℂ := ⇑eF ∘ w ∘ ⇑eE.symm with hh
  set ψ : ℂ → M := ⇑e.symm ∘ ⇑eE.symm with hψ
  have hI : Set.range (⇑I) = Set.univ := ModelWithCorners.Boundaryless.range_eq_univ
  have hJ : Set.range (⇑J) = Set.univ := ModelWithCorners.Boundaryless.range_eq_univ
  have hx₀src : x₀ ∈ e.source := he ▸ extChartAt_source I x₀ ▸ mem_chart_source H x₀
  have hfx₀src : f x₀ ∈ e'.source :=
    he' ▸ extChartAt_source J (f x₀) ▸ mem_chart_source G (f x₀)
  have hcont : Continuous f := hf.continuous
  have hTopen : IsOpen e.target := isOpen_extChartAt_target x₀
  have hS'open : IsOpen e'.source := isOpen_extChartAt_source (f x₀)
  have hp₀mem : p₀ ∈ e.target := e.map_source hx₀src
  have hU₀open : IsOpen (f ⁻¹' e'.source) := hS'open.preimage hcont
  have hx₀U₀ : x₀ ∈ f ⁻¹' e'.source := hfx₀src
  -- The domain in the model where both charts honestly apply.
  set V_E : Set E := e.target ∩ ⇑e.symm ⁻¹' (f ⁻¹' e'.source) with hV_E
  have hp₀VE : p₀ ∈ V_E := ⟨hp₀mem, by
    change e.symm p₀ ∈ f ⁻¹' e'.source
    have hleft : e.symm p₀ = x₀ := e.left_inv hx₀src
    rw [hleft]; exact hx₀U₀⟩
  have hVEopen : IsOpen V_E := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hpT : e.target ∈ 𝓝 p := hTopen.mem_nhds hp.1
    have hpre : ⇑e.symm ⁻¹' (f ⁻¹' e'.source) ∈ 𝓝 p := by
      have hca : ContinuousAt ⇑e.symm p :=
        (continuousOn_extChartAt_symm x₀).continuousAt hpT
      have hmem : f ⁻¹' e'.source ∈ 𝓝 (⇑e.symm p) :=
        hU₀open.mem_nhds hp.2
      exact mem_map.mp (hca hmem)
    exact inter_mem hpT hpre
  set V : Set ℂ := ⇑eE '' V_E with hV
  have hVopen : IsOpen V := by
    have hmap := eE.toHomeomorph.isOpenMap V_E hVEopen
    have hcoe : ⇑eE '' V_E = ⇑eE.toHomeomorph '' V_E := rfl
    rw [hcoe] at *
    exact hmap
  have hr₀V : r₀ ∈ V := mem_image_of_mem _ hp₀VE
  -- `w` is differentiable at every point of `V_E`, via the manifold
  -- differentiability of `f` read in the fixed charts.
  have hwdiff : DifferentiableOn ℂ w V_E := by
    intro p hp
    have hpT : p ∈ e.target := hp.1
    have hpmem : ⇑e.symm p ∈ f ⁻¹' e'.source := hp.2
    set x : M := ⇑e.symm p with hx
    have hxsrc : x ∈ e.source := e.map_target hpT
    have h1 : x ∈ (chartAt H x₀).source := by
      have hsrc : e.source = (chartAt H x₀).source := extChartAt_source I x₀
      rw [← hsrc]; exact hxsrc
    have h2 : f x ∈ (chartAt G (f x₀)).source := by
      have hsrc : e'.source = (chartAt G (f x₀)).source := extChartAt_source J (f x₀)
      rw [← hsrc]; exact hpmem
    have hmd := (mdifferentiableAt_iff_of_mem_source h1 h2).mp (hf x)
    obtain ⟨-, hdiff⟩ := hmd
    have hpt : (extChartAt I x₀) x = p := e.right_inv hpT
    rw [hI, differentiableWithinAt_univ, hpt] at hdiff
    -- hdiff : DifferentiableAt ℂ (⇑e' ∘ f ∘ ⇑e.symm) p
    have hdiffw : DifferentiableAt ℂ w p := hdiff
    exact hdiffw.differentiableWithinAt
  -- Transfer to `h` on `V` through the linear identifications.
  have hhdiff : DifferentiableOn ℂ h V := by
    intro z hz
    obtain ⟨p, hpVE, rfl⟩ := hz
    have hpmem : ⇑eE.symm (⇑eE p) = p := by simp
    have hwp : DifferentiableAt ℂ w p :=
      (hwdiff p hpVE).differentiableAt (hVEopen.mem_nhds hpVE)
    have hlin1 : DifferentiableAt ℂ (⇑eE.symm) (⇑eE p) :=
      eE.symm.toContinuousLinearMap.differentiableAt
    have hlin2 : DifferentiableAt ℂ (⇑eF) (w p) :=
      eF.toContinuousLinearMap.differentiableAt
    have hwp' : DifferentiableAt ℂ w (⇑eE.symm (⇑eE p)) := by
      rw [hpmem]; exact hwp
    have hcomp1 : DifferentiableAt ℂ (w ∘ ⇑eE.symm) (⇑eE p) :=
      hwp'.comp (⇑eE p) hlin1
    have e1 : (w ∘ ⇑eE.symm) (⇑eE p) = w p := by simp
    have hlin2' : DifferentiableAt ℂ (⇑eF) ((w ∘ ⇑eE.symm) (⇑eE p)) := by
      rw [e1]; exact hlin2
    have hcomp2 : DifferentiableAt ℂ (⇑eF ∘ (w ∘ ⇑eE.symm)) (⇑eE p) :=
      hlin2'.comp (⇑eE p) hcomp1
    exact hcomp2.differentiableWithinAt
  have hanalytic : AnalyticOnNhd ℂ h V := hhdiff.analyticOnNhd hVopen
  -- Honesty of the chart expression on `V`.
  have hhon : ∀ z ∈ V,
      eE.symm z ∈ e.target ∧
      f (⇑e.symm (eE.symm z)) ∈ e'.source ∧
      h z = eF (⇑e' (f (⇑e.symm (eE.symm z)))) := by
    intro z hz
    obtain ⟨p, hpVE, rfl⟩ := hz
    have hpmem : ⇑eE.symm (⇑eE p) = p := by simp
    refine ⟨?_, ?_, ?_⟩
    · rw [hpmem]; exact hpVE.1
    · have e1 : ⇑e.symm (⇑eE.symm (⇑eE p)) = ⇑e.symm p := by rw [hpmem]
      rw [e1]; exact hpVE.2
    · change (⇑eF ∘ w ∘ ⇑eE.symm) (⇑eE p) = _
      have e1 : (⇑eE.symm) (⇑eE p) = p := by simp
      simp only [Function.comp_apply, e1]
      rfl
  have hr₀eq : h r₀ = eF q₀ := by
    have h1 := (hhon r₀ hr₀V).2.2
    have e1 : ⇑eE.symm r₀ = p₀ := by simp [hr₀]
    have e2 : ⇑e.symm p₀ = x₀ := e.left_inv hx₀src
    rw [e1, e2] at h1
    have hq : q₀ = ⇑e' (f x₀) := rfl
    rw [h1, hq]
  -- Filter identities: the parametrizations are local homeomorphisms.
  have hmapE : Filter.map ⇑eE.symm (𝓝 r₀) = 𝓝 p₀ := by
    have hbase := eE.symm.toHomeomorph.map_nhds_eq r₀
    have c1 : ⇑eE.symm = ⇑eE.symm.toHomeomorph := rfl
    have c2 : p₀ = ⇑eE.symm.toHomeomorph r₀ := by simp [hr₀]
    rw [c1, c2] at *
    exact hbase
  have hmape : Filter.map ⇑e.symm (𝓝 p₀) = 𝓝 x₀ := by
    have hbase := map_extChartAt_symm_nhdsWithin_range (I := I) x₀
    rw [hI, nhdsWithin_univ] at hbase
    have hpeq : p₀ = (extChartAt I x₀) x₀ := rfl
    rw [hpeq] at *
    exact hbase
  have hmapψ : Filter.map (⇑e.symm ∘ ⇑eE.symm) (𝓝 r₀) = 𝓝 x₀ := by
    rw [← Filter.map_map, hmapE, hmape]
  have hmapF : Filter.map ⇑eF.symm (𝓝 (h r₀)) = 𝓝 q₀ := by
    have hbase := eF.symm.toHomeomorph.map_nhds_eq (h r₀)
    have c2 : q₀ = ⇑eF.symm.toHomeomorph (h r₀) := by
      have c0 : ⇑eF.symm.toHomeomorph (h r₀) = ⇑eF.symm (h r₀) := rfl
      rw [c0, hr₀eq]
      simp
    have c1 : ⇑eF.symm = ⇑eF.symm.toHomeomorph := rfl
    rw [c1, c2] at *
    exact hbase
  have hmape' : Filter.map ⇑e'.symm (𝓝 q₀) = 𝓝 (f x₀) := by
    have hbase := map_extChartAt_symm_nhdsWithin_range (I := J) (f x₀)
    rw [hJ, nhdsWithin_univ] at hbase
    have hqeq : q₀ = (extChartAt J (f x₀)) (f x₀) := rfl
    rw [hqeq] at *
    exact hbase
  have hmapφ : Filter.map (⇑e'.symm ∘ ⇑eF.symm) (𝓝 (h r₀)) = 𝓝 (f x₀) := by
    rw [← Filter.map_map, hmapF, hmape']
  exact ⟨eE, eF, V, h, hVopen, hr₀V, hanalytic, hr₀eq, hhon, hmapψ, hmapφ⟩

/-- Local dichotomy: at any point, an `MDiff` map between one-dimensional
complex manifolds is either locally constant or locally open. -/
private theorem localDichotomy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℂ F G} [J.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    (hE : Module.finrank ℂ E = 1) (hF : Module.finrank ℂ F = 1)
    {f : M → N} (hf : MDiff f) (x₀ : M) :
    (∀ᶠ y in 𝓝 x₀, f y = f x₀) ∨ 𝓝 (f x₀) ≤ Filter.map f (𝓝 x₀) := by
  obtain ⟨eE, eF, V, h, hVopen, hr₀V, hanalytic, hr₀eq, hhon, hmapψ, hmapφ⟩ :=
    chartPackage hE hF hf x₀
  set e := extChartAt I x₀ with he
  set e' := extChartAt J (f x₀) with he'
  set r₀ : ℂ := eE (e x₀) with hr₀
  set ψ : ℂ → M := ⇑e.symm ∘ ⇑eE.symm with hψ
  have hfx₀src : f x₀ ∈ e'.source :=
    he' ▸ extChartAt_source J (f x₀) ▸ mem_chart_source G (f x₀)
  have hAt : AnalyticAt ℂ h r₀ := hanalytic r₀ hr₀V
  rcases hAt.eventually_constant_or_nhds_le_map_nhds_aux with hconst | hopen
  · -- `h` locally constant implies `f` locally constant.
    left
    have hVmem : V ∈ 𝓝 r₀ := hVopen.mem_nhds hr₀V
    have hev : ∀ᶠ z in 𝓝 r₀, f (ψ z) = f x₀ := by
      filter_upwards [hconst, hVmem] with z hz hVz
      have hmem := hhon z hVz
      obtain ⟨hT, hS, hheq⟩ := hmem
      have e1 : h z = eF (⇑e' (f (ψ z))) := by
        have hψz : ψ z = ⇑e.symm (eE.symm z) := rfl
        rw [hψz] at *
        exact hheq
      rw [hr₀eq] at hz
      have hinjF : Function.Injective ⇑eF := eF.toHomeomorph.injective
      have heq1 : ⇑e' (f (ψ z)) = ⇑e' (f x₀) := hinjF (e1.symm.trans hz)
      have hinj : InjOn ⇑e' e'.source := e'.injOn
      exact hinj hS hfx₀src heq1
    have hmem : {y | f y = f x₀} ∈ 𝓝 x₀ := by
      have h1 : {y | f y = f x₀} ∈ Filter.map ψ (𝓝 r₀) := by
        rw [mem_map]
        exact hev
      rw [hmapψ] at h1
      exact h1
    exact hmem
  · -- `h` locally open implies `f` locally open.
    right
    have hVmem : V ∈ 𝓝 r₀ := hVopen.mem_nhds hr₀V
    have hgerm : (f ∘ ψ) =ᶠ[𝓝 r₀] ((⇑e'.symm ∘ ⇑eF.symm) ∘ h) := by
      filter_upwards [hVmem] with z hVz
      have hmem := hhon z hVz
      obtain ⟨hT, hS, hheq⟩ := hmem
      change f (⇑e.symm (eE.symm z)) = ⇑e'.symm (⇑eF.symm (h z))
      rw [hheq]
      have e1 : ⇑eF.symm (eF (⇑e' (f (⇑e.symm (eE.symm z))))) =
          ⇑e' (f (⇑e.symm (eE.symm z))) := by simp
      rw [e1]
      exact (e'.left_inv hS).symm
    have hmapEq : Filter.map (f ∘ ψ) (𝓝 r₀) =
        Filter.map (⇑e'.symm ∘ ⇑eF.symm) (Filter.map h (𝓝 r₀)) := by
      rw [Filter.map_congr hgerm, Filter.map_map]
    have hle : Filter.map (⇑e'.symm ∘ ⇑eF.symm) (𝓝 (h r₀)) ≤
        Filter.map (⇑e'.symm ∘ ⇑eF.symm) (Filter.map h (𝓝 r₀)) :=
      Filter.map_mono hopen
    rw [hmapφ] at hle
    have hmapf : Filter.map f (𝓝 x₀) = Filter.map (f ∘ ψ) (𝓝 r₀) := by
      rw [← hmapψ, Filter.map_map]
    rw [hmapf, hmapEq]
    exact hle

/-- **Open mapping theorem for one-dimensional complex manifolds.** Let $M$ and $N$ be complex
manifolds without boundary modeled on complex normed spaces of dimension one, with complex $C^1$
(that is, holomorphic) transition maps, and suppose $M$ is connected. Then every holomorphic
(everywhere complex differentiable) map $f : M \to N$ that is not constant is an open map. -/
theorem isOpenMap_of_finrank_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℂ F G} [J.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [ConnectedSpace M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    (hE : Module.finrank ℂ E = 1) (hF : Module.finrank ℂ F = 1)
    {f : M → N} (hf : MDiff f) (hf_nonconst : ∃ x y : M, f x ≠ f y) :
    IsOpenMap f := by
  have dich : ∀ x₀, (∀ᶠ y in 𝓝 x₀, f y = f x₀) ∨ 𝓝 (f x₀) ≤ Filter.map f (𝓝 x₀) :=
    fun x₀ => localDichotomy hE hF hf x₀
  by_cases hS : ∃ x₀, ∀ᶠ y in 𝓝 x₀, f y = f x₀
  · -- Some point sees local constancy: propagate to a global constant along
    -- the connected manifold, contradicting nonconstancy.
    obtain ⟨x₀, hx₀⟩ := hS
    set c₀ : N := f x₀ with hc₀
    set Z : Set M := {x | ∀ᶠ y in 𝓝 x, f y = c₀} with hZ
    have hx₀Z : x₀ ∈ Z := hx₀
    have hZopen : IsOpen Z := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hx
      have hUsubZ : U ⊆ Z := by
        intro x' hx'
        have hUmem : U ∈ 𝓝 x' := hUopen.mem_nhds hx'
        exact mem_of_superset hUmem hUsub
      exact mem_of_superset (hUopen.mem_nhds hxU) hUsubZ
    have hZclosed : IsClosed Z := by
      rw [← closure_subset_iff_isClosed]
      intro x₁ hx₁
      obtain ⟨eE₁, eF₁, V₁, h₁, hV₁open, hr₁V, hanalytic, hr₁eq, hhon, hmapψ,
        hmapφ⟩ := chartPackage hE hF hf x₁
      set e₁ := extChartAt I x₁ with he₁
      set e₁' := extChartAt J (f x₁) with he₁'
      set r₁ : ℂ := eE₁ (e₁ x₁) with hr₁
      set ψ₁ : ℂ → M := ⇑e₁.symm ∘ ⇑eE₁.symm with hψ₁
      -- `c₀` lies in the target chart at `f x₁`.
      have hfx₁src : f x₁ ∈ e₁'.source :=
        he₁' ▸ extChartAt_source J (f x₁) ▸ mem_chart_source G (f x₁)
      have hU'open : IsOpen (f ⁻¹' e₁'.source) :=
        (isOpen_extChartAt_source (f x₁)).preimage hf.continuous
      obtain ⟨z, hzU', hzZ⟩ :=
        mem_closure_iff_nhds.mp hx₁ _ (hU'open.mem_nhds hfx₁src)
      have hzZev : ∀ᶠ y in 𝓝 z, f y = c₀ := hzZ
      have hfz : f z = c₀ := hzZev.self_of_nhds
      have hc₀src : c₀ ∈ e₁'.source := by
        rw [← hfz]; exact hzU'
      set const' : ℂ := eF₁ (⇑e₁' c₀) with hconst'
      -- Work inside a ball contained in `V₁`.
      obtain ⟨R, hRpos, hBsub⟩ := Metric.isOpen_iff.mp hV₁open r₁ hr₁V
      have hBmem : Metric.ball r₁ R ∈ 𝓝 r₁ := Metric.ball_mem_nhds r₁ hRpos
      have hBpre : IsPreconnected (Metric.ball r₁ R) :=
        (convex_ball r₁ R).isPreconnected
      have hanB : AnalyticOnNhd ℂ h₁ (Metric.ball r₁ R) := hanalytic.mono hBsub
      have hconstB : AnalyticOnNhd ℂ (fun _ => const') (Metric.ball r₁ R) :=
        analyticOnNhd_const
      -- The ball meets `ψ₁ ⁻¹' Z`, since `x₁` lies in the closure of `Z`.
      have hex : (Metric.ball r₁ R ∩ ψ₁ ⁻¹' Z).Nonempty := by
        by_contra hcon
        rw [Set.not_nonempty_iff_eq_empty] at hcon
        have hsub : Metric.ball r₁ R ⊆ ψ₁ ⁻¹' Zᶜ := by
          intro w hwB
          rw [mem_preimage, mem_compl_iff]
          intro hwZ
          have hmem : w ∈ Metric.ball r₁ R ∩ ψ₁ ⁻¹' Z := ⟨hwB, hwZ⟩
          rw [hcon] at hmem
          exact Set.notMem_empty w hmem
        have hpremem : ψ₁ ⁻¹' Zᶜ ∈ 𝓝 r₁ := mem_of_superset hBmem hsub
        have hcompl : Zᶜ ∈ Filter.map ψ₁ (𝓝 r₁) := mem_map.mpr hpremem
        rw [hmapψ] at hcompl
        obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.mp hx₁ _ hcompl
        exact hy1 hy2
      obtain ⟨z₂, hz₂B, hz₂Z⟩ := hex
      -- Near `x₂ = ψ₁ z₂ ∈ Z`, `f` equals `c₀`; hence `h₁` equals `const'`
      -- near `z₂`, and the identity theorem spreads this over the ball.
      obtain ⟨V₂, hV₂sub, hV₂open, hx₂V₂⟩ := mem_nhds_iff.mp hz₂Z
      have hψcont : ContinuousAt ψ₁ z₂ := by
        have hmemT : ⇑eE₁.symm z₂ ∈ e₁.target := (hhon z₂ (hBsub hz₂B)).1
        have hc1 : ContinuousAt ⇑eE₁.symm z₂ :=
          eE₁.symm.toContinuousLinearMap.continuous.continuousAt
        have hc2 : ContinuousAt ⇑e₁.symm (⇑eE₁.symm z₂) :=
          (continuousOn_extChartAt_symm x₁).continuousAt
            ((isOpen_extChartAt_target x₁).mem_nhds hmemT)
        exact hc2.comp hc1
      have hV₂mem : V₂ ∈ 𝓝 (ψ₁ z₂) := hV₂open.mem_nhds hx₂V₂
      have hpreV₂ : ψ₁ ⁻¹' V₂ ∈ 𝓝 z₂ := mem_map.mp (hψcont hV₂mem)
      have hV₁mem : V₁ ∈ 𝓝 z₂ := hV₁open.mem_nhds (hBsub hz₂B)
      have hev : h₁ =ᶠ[𝓝 z₂] fun _ => const' := by
        filter_upwards [hV₁mem, hpreV₂] with w hwV₁ hwV₂
        have hmem := hhon w hwV₁
        obtain ⟨hT, hS, hheq⟩ := hmem
        have hfw : f (⇑e₁.symm (⇑eE₁.symm w)) = c₀ := hV₂sub hwV₂
        change h₁ w = const'
        rw [show h₁ w = eF₁ (⇑e₁' (f (⇑e₁.symm (⇑eE₁.symm w)))) from hheq, hfw]
      have heqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
        hanB hconstB hBpre hz₂B hev
      have hevball : ∀ᶠ z in 𝓝 r₁, h₁ z = const' := by
        filter_upwards [hBmem] with z hzB
        exact heqOn hzB
      -- Transfer back to `f`: `x₁` sees the constant value `c₀` nearby.
      have hV₁memr₁ : V₁ ∈ 𝓝 r₁ := hV₁open.mem_nhds hr₁V
      have hevf : ∀ᶠ z in 𝓝 r₁, f (ψ₁ z) = c₀ := by
        filter_upwards [hevball, hV₁memr₁] with z hz hVz
        have hmem := hhon z hVz
        obtain ⟨hT, hS, hheq⟩ := hmem
        have hheq' : h₁ z = eF₁ (⇑e₁' (f (ψ₁ z))) := by
          have eψ : ψ₁ z = ⇑e₁.symm (⇑eE₁.symm z) := rfl
          rw [eψ]
          exact hheq
        have hconsteq : const' = eF₁ (⇑e₁' c₀) := rfl
        rw [hconsteq] at hz
        have hinjF : Function.Injective ⇑eF₁ := eF₁.toHomeomorph.injective
        have heq1 : ⇑e₁' (f (ψ₁ z)) = ⇑e₁' c₀ := hinjF (hheq'.symm.trans hz)
        have hinj : InjOn ⇑e₁' e₁'.source := e₁'.injOn
        exact hinj hS hc₀src heq1
      have hmemZ : {y | f y = c₀} ∈ 𝓝 x₁ := by
        have h1 : {y | f y = c₀} ∈ Filter.map ψ₁ (𝓝 r₁) := by
          rw [mem_map]; exact hevf
        rw [hmapψ] at h1; exact h1
      exact hmemZ
    -- `Z` is clopen and nonempty, hence everything; `f` is constant.
    have hZclopen : IsClopen Z := ⟨hZclosed, hZopen⟩
    have hZuniv : Z = Set.univ := hZclopen.eq_univ ⟨x₀, hx₀Z⟩
    obtain ⟨a, b, hab⟩ := hf_nonconst
    have haZ : a ∈ Z := by rw [hZuniv]; exact mem_univ a
    have hbZ : b ∈ Z := by rw [hZuniv]; exact mem_univ b
    have haev : ∀ᶠ y in 𝓝 a, f y = c₀ := haZ
    have hbev : ∀ᶠ y in 𝓝 b, f y = c₀ := hbZ
    have ha : f a = c₀ := haev.self_of_nhds
    have hb : f b = c₀ := hbev.self_of_nhds
    exact absurd (ha.trans hb.symm) hab
  · -- Nowhere locally constant: every point is a point of local openness.
    rw [isOpenMap_iff_nhds_le]
    intro x
    rcases dich x with hconst | hopen
    · exact absurd hconst (fun h => hS ⟨x, h⟩)
    · exact hopen

end MDifferentiable

namespace MathlibExt.Geometry.Manifold.ComplexRigidityWanted

/--
**Open mapping theorem for Riemann surfaces.** Let $M$ and $N$ be complex manifolds without
boundary modeled on complex normed spaces of dimension one, with complex $C^1$ (that is,
holomorphic) transition maps, and suppose $M$ is connected. Then every holomorphic (everywhere
complex differentiable) map $f : M \to N$ that is not constant is an open map.

Source: O. Forster, Lectures on Riemann Surfaces, open mapping theorem for Riemann surfaces; Lean
states one-complex-dimensional specialization.
It is `MDifferentiable.isOpenMap_of_finrank_eq_one`, kept under the source's name.
Proves `Wanted` entry `holomorphic_open_mapping_one_dim`.
-/
theorem holomorphic_open_mapping_one_dim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℂ F G} [J.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [ConnectedSpace M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    (hE : Module.finrank ℂ E = 1) (hF : Module.finrank ℂ F = 1)
    {f : M → N} (hf : MDiff f) (hf_nonconst : ∃ x y : M, f x ≠ f y) :
    IsOpenMap f :=
  MDifferentiable.isOpenMap_of_finrank_eq_one hE hF hf hf_nonconst

end MathlibExt.Geometry.Manifold.ComplexRigidityWanted
