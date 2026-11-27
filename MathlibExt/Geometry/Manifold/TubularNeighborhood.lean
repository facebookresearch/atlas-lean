/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Geometry.Manifold.Sheaf.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linarith

@[expose] public section

open Manifold Topology Filter Metric
open scoped Manifold ContDiff

-- N0: coordinate normal-equation map (avoids semilinear innerSL typing issue)
private noncomputable def normalEqMapCoord
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (γ : E → F) : F × E → (Fin (Module.finrank ℝ E) → ℝ) :=
  fun q i => inner ℝ (q.1 - γ q.2) ((fderiv ℝ γ q.2) ((Module.finBasis ℝ E) i))

-- N1: smoothness at (y, u)
private theorem contDiffAt_normalEqMapCoord
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {Ω : Set E} {γ : E → F} {y : F} {u : E}
    (hΩ : IsOpen Ω) (hγ : ContDiffOn ℝ (∞ : ℕ∞ω) γ Ω) (hu : u ∈ Ω) :
    ContDiffAt ℝ (∞ : ℕ∞ω) (normalEqMapCoord γ) (y, u) := by
  have hγat : ContDiffAt ℝ (∞ : ℕ∞ω) γ u := hγ.contDiffAt (hΩ.mem_nhds hu)
  have hDf : ContDiffAt ℝ (∞ : ℕ∞ω) (fun q : F × E => fderiv ℝ γ q.2) (y, u) := by
    have h1 : ContDiffOn ℝ (∞ : ℕ∞ω) (fderiv ℝ γ) Ω :=
      hγ.fderiv_of_isOpen hΩ (by simp)
    exact ContDiffAt.comp (y, u) (h1.contDiffAt (hΩ.mem_nhds hu)) contDiffAt_snd
  rw [contDiffAt_pi]
  intro i
  change ContDiffAt ℝ (∞ : ℕ∞ω)
    (fun q : F × E => inner ℝ (q.1 - γ q.2)
      ((fderiv ℝ γ q.2) ((Module.finBasis ℝ E) i))) (y, u)
  apply ContDiffAt.inner ℝ
  · exact contDiffAt_fst.sub (ContDiffAt.comp (y, u) hγat contDiffAt_snd)
  · exact ContDiffAt.clm_apply hDf contDiffAt_const

private theorem normalEqMapCoord_self_eq_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {γ : E → F} {u0 : E} :
    normalEqMapCoord γ (γ u0, u0) = 0 := by
  funext i
  change inner ℝ (γ u0 - γ u0) ((fderiv ℝ γ u0) ((Module.finBasis ℝ E) i)) = 0
  rw [sub_self]
  exact inner_zero_left _

-- N2b: partial derivative in second variable is injective
private theorem injective_partial_normalEqMapCoord
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {Ω : Set E} {γ : E → F} {u0 : E}
    (hΩ : IsOpen Ω) (hγ : ContDiffOn ℝ (∞ : ℕ∞ω) γ Ω) (hu0 : u0 ∈ Ω)
    (hinjA : Function.Injective (fderiv ℝ γ u0)) :
    Function.Injective ((fderiv ℝ (normalEqMapCoord γ) (γ u0, u0)).comp
      (ContinuousLinearMap.inr ℝ F E)) := by
  classical
  have hγdiff : DifferentiableAt ℝ γ u0 :=
    (hγ.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hu0)
  have hG : ContDiffAt ℝ (∞ : ℕ∞ω) (normalEqMapCoord γ) (γ u0, u0) :=
    contDiffAt_normalEqMapCoord hΩ hγ hu0
  have hGdiff : DifferentiableAt ℝ (normalEqMapCoord γ) (γ u0, u0) :=
    hG.differentiableAt (by simp)
  have hcurve : HasFDerivAt (fun u => normalEqMapCoord γ (γ u0, u))
      ((fderiv ℝ (normalEqMapCoord γ) (γ u0, u0)).comp
        (ContinuousLinearMap.inr ℝ F E)) u0 :=
    hGdiff.hasFDerivAt.comp u0 (hasFDerivAt_prodMk_right (γ u0) u0)
  have hcoord : ∀ i, HasFDerivAt
      (⇑(ContinuousLinearMap.proj i) ∘ (fun u => normalEqMapCoord γ (γ u0, u)))
      ((ContinuousLinearMap.proj i).comp
        ((fderiv ℝ (normalEqMapCoord γ) (γ u0, u0)).comp
          (ContinuousLinearMap.inr ℝ F E))) u0 :=
    fun i => (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.proj i)).comp u0 hcurve
  have hDfat : ContDiffAt ℝ (∞ : ℕ∞ω) (fderiv ℝ γ) u0 :=
    (hγ.fderiv_of_isOpen hΩ (by simp)).contDiffAt (hΩ.mem_nhds hu0)
  have hDfhas : HasFDerivAt (fderiv ℝ γ) (fderiv ℝ (fderiv ℝ γ) u0) u0 :=
    (hDfat.differentiableAt (by simp)).hasFDerivAt
  have hf : HasFDerivAt (fun u => γ u0 - γ u) (-(fderiv ℝ γ u0)) u0 :=
    hγdiff.hasFDerivAt.const_sub (γ u0)
  have hg : ∀ i, HasFDerivAt
      (⇑(ContinuousLinearMap.apply ℝ F ((Module.finBasis ℝ E) i)) ∘ (fderiv ℝ γ))
      ((ContinuousLinearMap.apply ℝ F ((Module.finBasis ℝ E) i)).comp
        (fderiv ℝ (fderiv ℝ γ) u0)) u0 :=
    fun i => (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.apply ℝ F ((Module.finBasis ℝ E) i))).comp u0 hDfhas
  have hdirect : ∀ i, HasFDerivAt
      (fun t => inner ℝ ((fun u => γ u0 - γ u) t)
        ((⇑(ContinuousLinearMap.apply ℝ F ((Module.finBasis ℝ E) i)) ∘
          (fderiv ℝ γ)) t))
      (fderivInnerCLM ℝ ((γ u0 - γ u0),
        (⇑(ContinuousLinearMap.apply ℝ F ((Module.finBasis ℝ E) i)) ∘
          (fderiv ℝ γ)) u0) ∘SL
        ((-(fderiv ℝ γ u0)).prod
          ((ContinuousLinearMap.apply ℝ F ((Module.finBasis ℝ E) i)).comp
            (fderiv ℝ (fderiv ℝ γ) u0)))) u0 :=
    fun i => HasFDerivAt.inner ℝ hf (hg i)
  have hTeq : ∀ i, (ContinuousLinearMap.proj i).comp
        ((fderiv ℝ (normalEqMapCoord γ) (γ u0, u0)).comp
          (ContinuousLinearMap.inr ℝ F E)) =
      fderivInnerCLM ℝ ((γ u0 - γ u0),
        (⇑(ContinuousLinearMap.apply ℝ F ((Module.finBasis ℝ E) i)) ∘
          (fderiv ℝ γ)) u0) ∘SL
        ((-(fderiv ℝ γ u0)).prod
          ((ContinuousLinearMap.apply ℝ F ((Module.finBasis ℝ E) i)).comp
            (fderiv ℝ (fderiv ℝ γ) u0))) :=
    fun i => HasFDerivAt.unique (hcoord i) (hdirect i)
  have hcore : ∀ δ : E, ((fderiv ℝ (normalEqMapCoord γ) (γ u0, u0)).comp
        (ContinuousLinearMap.inr ℝ F E)) δ = 0 →
      (fderiv ℝ γ u0) δ = 0 := by
    intro δ hδ
    have hzero : ∀ i : Fin (Module.finrank ℝ E),
        inner ℝ ((fderiv ℝ γ u0) δ)
          ((fderiv ℝ γ u0) ((Module.finBasis ℝ E) i)) = 0 := by
      intro i
      have e1 := DFunLike.congr_fun (hTeq i) δ
      simp only [ContinuousLinearMap.comp_apply] at e1 hδ
      rw [hδ, map_zero] at e1
      simp only [ContinuousLinearMap.prod_apply,
        fderivInnerCLM_apply, sub_self, inner_zero_left, zero_add,
        neg_apply, inner_neg_left] at e1
      exact neg_eq_zero.mp e1.symm
    have hself : inner ℝ ((fderiv ℝ γ u0) δ) ((fderiv ℝ γ u0) δ) = 0 := by
      have hexpand : (fderiv ℝ γ u0) δ =
          ∑ j, ((Module.finBasis ℝ E).repr δ j) • ((fderiv ℝ γ u0) ((Module.finBasis ℝ E) j)) := by
        conv_lhs => rw [← Module.Basis.sum_repr (Module.finBasis ℝ E) δ]
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact map_smul _ _ _
      nth_rewrite 2 [hexpand]
      rw [inner_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [inner_smul_right, hzero j, mul_zero]
    exact inner_self_eq_zero.mp hself
  intro η1 η2 h12
  have h0 : ((fderiv ℝ (normalEqMapCoord γ) (γ u0, u0)).comp
        (ContinuousLinearMap.inr ℝ F E)) (η1 - η2) = 0 := by
    rw [map_sub, h12, sub_self]
  have hA := hcore _ h0
  rw [map_sub] at hA
  exact hinjA (sub_eq_zero.mp hA)

-- N5: first-order condition for nearest points
private theorem normalEqMapCoord_eq_zero_of_isMinOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {Ω : Set E} {γ : E → F} {u : E} {y : F}
    (hΩ : IsOpen Ω) (hu : u ∈ Ω)
    (hγdiff : DifferentiableAt ℝ γ u)
    (hmin : ∀ v ∈ Ω, ‖y - γ u‖ ≤ ‖y - γ v‖) :
    normalEqMapCoord γ (y, u) = 0 := by
  have hsub : HasFDerivAt (fun v => y - γ v) (-(fderiv ℝ γ u)) u :=
    hγdiff.hasFDerivAt.const_sub y
  have hsq := hsub.norm_sq
  have hmin2 : IsMinOn (fun v => ‖y - γ v‖ ^ 2) Ω u := by
    intro v hv
    exact pow_le_pow_left₀ (norm_nonneg _) (hmin v hv) 2
  have hlocal : IsLocalMin (fun v => ‖y - γ v‖ ^ 2) u :=
    hmin2.isLocalMin (hΩ.mem_nhds hu)
  have hzero := hlocal.hasFDerivAt_eq_zero hsq
  funext i
  change inner ℝ (y - γ u) ((fderiv ℝ γ u) ((Module.finBasis ℝ E) i)) = 0
  have hi := DFunLike.congr_fun hzero ((Module.finBasis ℝ E) i)
  simp only [smul_apply, ContinuousLinearMap.comp_apply, neg_apply] at hi
  rcases smul_eq_zero.mp hi with h | h
  · exact absurd h two_ne_zero
  · have h2 : inner ℝ (y - γ u) (-((fderiv ℝ γ u) ((Module.finBasis ℝ E) i))) = 0 := h
    rw [inner_neg_right] at h2
    exact neg_eq_zero.mp h2

open Topology

private theorem isInvertible_of_injective_of_finrank_eq
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (h : Module.finrank ℝ E = Module.finrank ℝ X)
    (T : E →L[ℝ] X) (hinj : Function.Injective T) : T.IsInvertible := by
  have hinj' : Function.Injective (T : E →ₗ[ℝ] X) := by simpa using hinj
  have hsurj : Function.Surjective (T : E →ₗ[ℝ] X) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).mp hinj'
  have hker : LinearMap.ker (T : E →ₗ[ℝ] X) = ⊥ := LinearMap.ker_eq_bot.mpr hinj'
  have hrange : LinearMap.range (T : E →ₗ[ℝ] X) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have h2 := ContinuousLinearMap.isInvertible_equiv
    (f := ContinuousLinearEquiv.ofBijective T hker hrange)
  rw [ContinuousLinearEquiv.coe_ofBijective] at h2
  exact h2

-- N7: embedding pulls back balls
private theorem exists_ball_forall_dist_lt_mem_of_isEmbedding
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {e : X → Y} (he : IsEmbedding e) (x0 : X) {V : Set X} (hV : V ∈ 𝓝 x0) :
    ∃ δ > 0, ∀ x, dist (e x) (e x0) < δ → x ∈ V := by
  have hcomap : 𝓝 x0 = Filter.comap e (𝓝 (e x0)) :=
    IsInducing.nhds_eq_comap he.isInducing x0
  rw [hcomap] at hV
  rw [Filter.mem_comap] at hV
  obtain ⟨t, ht, hte⟩ := hV
  rw [Metric.mem_nhds_iff] at ht
  obtain ⟨δ, hδ, hball⟩ := ht
  exact ⟨δ, hδ, fun x hx => hte (hball (by simpa [Metric.mem_ball, dist_comm] using hx))⟩

open scoped ContDiff

-- N4: smooth implicit function on a whole ball, with uniqueness
private theorem exists_smooth_implicit_unique_on_ball
    {F E X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {G : F × E → X} {y0 : F} {u0 : E} {W : Set E}
    (hW : W ∈ 𝓝 u0)
    (hGsmooth : ∀ᶠ q in 𝓝 (y0, u0), ContDiffAt ℝ (∞ : ℕ∞ω) G q)
    (hG0 : G (y0, u0) = 0)
    (hInv : ((fderiv ℝ G (y0, u0)) ∘SL (ContinuousLinearMap.inr ℝ F E)).IsInvertible) :
    ∃ ρ > 0, ∃ σ > 0, ∃ ψ : F → E,
      (Metric.ball u0 ρ ⊆ W) ∧
      (∀ y ∈ Metric.ball y0 σ, ψ y ∈ Metric.ball u0 ρ ∧ ContDiffAt ℝ (∞ : ℕ∞ω) ψ y) ∧
      (∀ y ∈ Metric.ball y0 σ, ∀ u ∈ Metric.ball u0 ρ, G (y, u) = 0 → u = ψ y) := by
  have hne : (∞ : ℕ∞ω) ≠ 0 := by simp
  have cdf0 : ContDiffAt ℝ (∞ : ℕ∞ω) G (y0, u0) := hGsmooth.self_of_nhds
  have hψself : cdf0.implicitFunction hne hInv y0 = u0 :=
    cdf0.implicitFunction_apply_self hne hInv
  have hψcont0 : ContDiffAt ℝ (∞ : ℕ∞ω) (cdf0.implicitFunction hne hInv) y0 :=
    cdf0.contDiffAt_implicitFunction hne hInv
  have hN : {v : F × E | G v = G (y0, u0)
      ↔ cdf0.implicitFunction hne hInv v.1 = v.2} ∈ 𝓝 (y0, u0) :=
    cdf0.eventually_apply_eq_iff_implicitFunction hne hInv
  have hDf1 : ContDiffAt ℝ (1 : ℕ∞ω) (fderiv ℝ G) (y0, u0) :=
    cdf0.fderiv_right (by simp)
  have hQ : ContDiffAt ℝ (1 : ℕ∞ω)
      (fun q : F × E => (fderiv ℝ G q) ∘SL (ContinuousLinearMap.inr ℝ F E)) (y0, u0) :=
    ContDiffAt.clm_comp hDf1 contDiffAt_const
  have hQcont : ContinuousAt
      (fun q : F × E => (fderiv ℝ G q) ∘SL (ContinuousLinearMap.inr ℝ F E)) (y0, u0) :=
    hQ.continuousAt
  have hSinv : {q : F × E |
      ((fderiv ℝ G q) ∘SL (ContinuousLinearMap.inr ℝ F E)).IsInvertible} ∈ 𝓝 (y0, u0) :=
    hQcont.preimage_mem_nhds hInv.eventually_nhds
  have hWprod : (Set.univ ×ˢ W) ∈ 𝓝 (y0, u0) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod Filter.univ_mem hW
  have hGsmooth' : {q : F × E | ContDiffAt ℝ (∞ : ℕ∞ω) G q} ∈ 𝓝 (y0, u0) := hGsmooth
  have hInter := Filter.inter_mem hN
    (Filter.inter_mem hSinv (Filter.inter_mem hGsmooth' hWprod))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hInter
  have hbox : ∀ (y : F) (u : E), y ∈ Metric.ball y0 r → u ∈ Metric.ball u0 r →
      (G (y, u) = G (y0, u0) ↔ cdf0.implicitFunction hne hInv y = u) ∧
      ((fderiv ℝ G (y, u) ∘SL
        (ContinuousLinearMap.inr ℝ F E)).IsInvertible) ∧
      (ContDiffAt ℝ (∞ : ℕ∞ω) G (y, u)) ∧
      ((y, u) ∈ Set.univ ×ˢ W) := by
    intro y u hy hu
    have hmem : (y, u) ∈ Metric.ball (y0, u0) r := by
      rw [← ball_prod_same]
      exact Set.mk_mem_prod hy hu
    exact hball hmem
  have hψcont : ContinuousAt (cdf0.implicitFunction hne hInv) y0 :=
    hψcont0.continuousAt
  have hpre : (cdf0.implicitFunction hne hInv) ⁻¹' (Metric.ball u0 r) ∈ 𝓝 y0 := by
    have hballmem : Metric.ball u0 r ∈ 𝓝 ((cdf0.implicitFunction hne hInv) y0) := by
      rw [hψself]
      exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)
    exact hψcont.preimage_mem_nhds hballmem
  obtain ⟨σ', hσ', hσball⟩ := Metric.mem_nhds_iff.mp hpre
  have hc : ∀ y ∈ Metric.ball y0 (min σ' r), ∀ u ∈ Metric.ball u0 r,
      G (y, u) = 0 → u = cdf0.implicitFunction hne hInv y := by
    intro y hy u hu hGu
    have hyr : y ∈ Metric.ball y0 r :=
      Metric.ball_subset_ball (min_le_right _ _) hy
    have hbox_yu := hbox y u hyr hu
    have hG00 : G (y, u) = G (y0, u0) := by rw [hGu, hG0]
    exact (hbox_yu.1.mp hG00).symm
  refine ⟨r, hr, min σ' r, lt_min hσ' hr, cdf0.implicitFunction hne hInv, ?_, ?_, hc⟩
  · intro v hv
    have hmem : (y0, v) ∈ Metric.ball (y0, u0) r := by
      rw [← ball_prod_same]
      exact Set.mk_mem_prod (Metric.mem_ball_self hr) hv
    exact ((hball hmem).2.2.2).2
  · intro y hy
    have hyr : y ∈ Metric.ball y0 r :=
      Metric.ball_subset_ball (min_le_right _ _) hy
    have hpre_y : (cdf0.implicitFunction hne hInv) y ∈ Metric.ball u0 r :=
      hσball (Metric.ball_subset_ball (min_le_left _ _) hy)
    refine ⟨hpre_y, ?_⟩
    have hbox_y := hbox y ((cdf0.implicitFunction hne hInv) y) hyr hpre_y
    have hGy : G (y, (cdf0.implicitFunction hne hInv) y) = 0 := by
      have hiff := hbox_y.1
      rw [hG0] at hiff
      exact hiff.mpr rfl
    have cdf1 : ContDiffAt ℝ (∞ : ℕ∞ω) G (y, (cdf0.implicitFunction hne hInv) y) :=
      hbox_y.2.2.1
    have hInv1 : ((fderiv ℝ G (y, (cdf0.implicitFunction hne hInv) y)) ∘SL
        (ContinuousLinearMap.inr ℝ F E)).IsInvertible := hbox_y.2.1
    have hψ1smooth : ContDiffAt ℝ (∞ : ℕ∞ω) (cdf1.implicitFunction hne hInv1) y :=
      cdf1.contDiffAt_implicitFunction hne hInv1
    have hψ1self : cdf1.implicitFunction hne hInv1 y
        = (cdf0.implicitFunction hne hInv) y :=
      cdf1.implicitFunction_apply_self hne hInv1
    have hev : ∀ᶠ x in 𝓝 y,
        G (x, cdf1.implicitFunction hne hInv1 x)
          = G (y, (cdf0.implicitFunction hne hInv) y) :=
      cdf1.eventually_apply_implicitFunction hne hInv1
    rw [hGy] at hev
    have hev1 : ∀ᶠ x in 𝓝 y, x ∈ Metric.ball y0 (min σ' r) :=
      Metric.isOpen_ball.mem_nhds hy
    have hev2 : ∀ᶠ x in 𝓝 y,
        cdf1.implicitFunction hne hInv1 x ∈ Metric.ball u0 r := by
      have hmem2 : Metric.ball u0 r ∈ 𝓝 ((cdf1.implicitFunction hne hInv1) y) := by
        rw [hψ1self]
        exact Metric.isOpen_ball.mem_nhds hpre_y
      exact hψ1smooth.continuousAt.preimage_mem_nhds hmem2
    have hcomb := hev.and (hev1.and hev2)
    have heq : (cdf0.implicitFunction hne hInv)
        =ᶠ[𝓝 y] (cdf1.implicitFunction hne hInv1) := by
      filter_upwards [hcomb] with x hx
      exact (hc x hx.2.1 _ hx.2.2 hx.1).symm
    exact hψ1smooth.congr_of_eventuallyEq heq

open Manifold Topology

private theorem chartRep_of_isSmoothEmbedding
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : M → F) (he : IsSmoothEmbedding I 𝓘(ℝ, F) (⊤ : ℕ∞) e) (x0 : M) :
    IsOpen (extChartAt I x0).target ∧
    ((extChartAt I x0) x0 ∈ (extChartAt I x0).target) ∧
    ContDiffOn ℝ (∞ : ℕ∞ω) (e ∘ (extChartAt I x0).symm) (extChartAt I x0).target ∧
    Function.Injective (fderiv ℝ (e ∘ (extChartAt I x0).symm) ((extChartAt I x0) x0)) ∧
    ∀ x ∈ (extChartAt I x0).source,
      (e ∘ (extChartAt I x0).symm) ((extChartAt I x0) x) = e x := by
  refine ⟨isOpen_extChartAt_target x0, mem_extChartAt_target x0, ?_, ?_, ?_⟩
  · have h1 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ((⊤ : ℕ∞) : ℕ∞ω)
        (e ∘ (extChartAt I x0).symm) (extChartAt I x0).target :=
      he.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt_symm x0)
    have h2 := contMDiffOn_iff_contDiffOn.mp h1
    change ContDiffOn ℝ (∞ : ℕ∞ω) _ _
    exact h2
  · have hne : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0 := by simp
    have hmd : MDiffAt e x0 :=
      (he.contMDiff.contMDiffAt (x := x0)).mdifferentiableAt hne
    have hinj := he.isImmersion.mfderiv_injective hne x0
    rw [MDifferentiableAt.mfderiv hmd] at hinj
    rw [ModelWithCorners.range_eq_univ, fderivWithin_univ] at hinj
    have hmodel : extChartAt 𝓘(ℝ, F) (e x0) = PartialEquiv.refl F :=
      extChartAt_model_space_eq_id ℝ (e x0)
    have hwrite : writtenInExtChartAt I 𝓘(ℝ, F) x0 e
        = e ∘ (extChartAt I x0).symm := by
      funext v
      change (extChartAt 𝓘(ℝ, F) (e x0)) (e ((extChartAt I x0).symm v)) = _
      rw [hmodel]
      rfl
    rw [hwrite] at hinj
    intro a b hab
    have e1 : ((tangentSpaceCastModel 𝓘(ℝ, F) (e x0)).symm
        ((fderiv ℝ (e ∘ (extChartAt I x0).symm) ((extChartAt I x0) x0))
          ((tangentSpaceCastModel I x0) ((tangentSpaceCastModel I x0).symm a)))) =
        ((tangentSpaceCastModel 𝓘(ℝ, F) (e x0)).symm
        ((fderiv ℝ (e ∘ (extChartAt I x0).symm) ((extChartAt I x0) x0))
          ((tangentSpaceCastModel I x0) ((tangentSpaceCastModel I x0).symm b)))) := by
      simp only [ContinuousLinearEquiv.apply_symm_apply, hab]
    have h2 := hinj e1
    exact (tangentSpaceCastModel I x0).symm.injective h2
  · intro x hx
    exact congrArg e ((extChartAt I x0).left_inv hx)
private theorem local_nearest_point_structure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {n : ℕ}
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : IsSmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (⊤ : ℕ∞) e)
    (x0 : M) :
    ∃ ε > 0, ∃ ψ : EuclideanSpace ℝ (Fin n) → E,
      ∀ y ∈ Metric.ball (e x0) ε, ψ y ∈ (extChartAt I x0).target ∧
        ContDiffAt ℝ (∞ : ℕ∞ω) ψ y ∧
        ∀ x : M, (∀ x' : M, dist y (e x) ≤ dist y (e x')) →
          x = (extChartAt I x0).symm (ψ y) := by
  obtain ⟨hΩopen, hu0mem, hγsmooth, hinjA, hγeq⟩ :=
    chartRep_of_isSmoothEmbedding e he x0
  set c := extChartAt I x0 with hcdef
  set Ω : Set E := c.target with hΩdef
  set u0 : E := c x0 with hu0def
  set γ : E → EuclideanSpace ℝ (Fin n) := e ∘ c.symm with hγdef
  have hγu0 : γ u0 = e x0 := hγeq x0 (mem_extChartAt_source x0)
  have hGsmoothEv : ∀ᶠ q in 𝓝 (γ u0, u0),
      ContDiffAt ℝ (∞ : ℕ∞ω) (normalEqMapCoord γ) q := by
    have hmem : (Set.univ ×ˢ Ω) ∈ 𝓝 (γ u0, u0) := by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod Filter.univ_mem (hΩopen.mem_nhds hu0mem)
    filter_upwards [hmem] with q hq
    exact contDiffAt_normalEqMapCoord hΩopen hγsmooth (Set.mem_prod.mp hq).2
  have hG0 : normalEqMapCoord γ (γ u0, u0) = 0 := normalEqMapCoord_self_eq_zero
  have hinjP : Function.Injective ((fderiv ℝ (normalEqMapCoord γ) (γ u0, u0)).comp
      (ContinuousLinearMap.inr ℝ _ E)) :=
    injective_partial_normalEqMapCoord hΩopen hγsmooth hu0mem hinjA
  have hfr : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (Module.finrank ℝ E) → ℝ) := by
    rw [Module.finrank_pi, Fintype.card_fin]
  have hinv := isInvertible_of_injective_of_finrank_eq hfr _ hinjP
  obtain ⟨ρ, hρpos, σ, hσpos, ψ, hsubW, hψball, huniq⟩ :=
    exists_smooth_implicit_unique_on_ball (hΩopen.mem_nhds hu0mem) hGsmoothEv hG0 hinv
  have hVmem : (c.source ∩ c ⁻¹' (Metric.ball u0 ρ)) ∈ 𝓝 x0 := Filter.inter_mem
    (extChartAt_source_mem_nhds x0)
    ((continuousAt_extChartAt x0).preimage_mem_nhds (Metric.ball_mem_nhds u0 hρpos))
  obtain ⟨δ, hδpos, hδball⟩ :=
    exists_ball_forall_dist_lt_mem_of_isEmbedding he.isEmbedding x0 hVmem
  refine ⟨min σ (δ / 2), lt_min hσpos (by linarith), ψ, ?_⟩
  intro y hy
  have hyd : dist y (e x0) < min σ (δ / 2) := Metric.mem_ball.mp hy
  have hydσ : dist y (γ u0) < σ := by
    rw [← hγu0] at hyd
    exact lt_of_lt_of_le hyd (min_le_left _ _)
  have hyσ : y ∈ Metric.ball (γ u0) σ := Metric.mem_ball.mpr hydσ
  have hyd2 : dist y (e x0) < δ / 2 := lt_of_lt_of_le hyd (min_le_right _ _)
  have hψy := hψball y hyσ
  have key : ∀ z : M, (∀ z' : M, dist y (e z) ≤ dist y (e z')) → c z = ψ y := by
    intro z hznear
    have hnear0 : dist y (e z) ≤ dist y (e x0) := hznear x0
    have hdist : dist (e z) (e x0) < δ := by
      calc dist (e z) (e x0) ≤ dist (e z) y + dist y (e x0) := dist_triangle _ _ _
        _ = dist y (e z) + dist y (e x0) := by rw [dist_comm (e z) y]
        _ < δ := by linarith
    have hzV := hδball z hdist
    have hzsrc : z ∈ c.source := hzV.1
    have hzc : c z ∈ Metric.ball u0 ρ := hzV.2
    have hγz : γ (c z) = e z := hγeq z hzsrc
    have hzΩ : c z ∈ Ω := hsubW hzc
    have hmin : ∀ v ∈ Ω, ‖y - γ (c z)‖ ≤ ‖y - γ v‖ := by
      intro v hv
      have hnear : dist y (e z) ≤ dist y (e (c.symm v)) := hznear _
      have hnear2 : ‖y - e z‖ ≤ ‖y - e (c.symm v)‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hnear
      rw [hγz]
      simpa [hγdef, Function.comp_apply] using hnear2
    have hγdiff : DifferentiableAt ℝ γ (c z) :=
      (hγsmooth.differentiableOn (by simp)).differentiableAt (hΩopen.mem_nhds hzΩ)
    have hGzero : normalEqMapCoord γ (y, c z) = 0 :=
      normalEqMapCoord_eq_zero_of_isMinOn hΩopen hzΩ hγdiff hmin
    exact huniq y hyσ (c z) hzc hGzero
  refine ⟨hsubW hψy.1, hψy.2, fun x hxnear => ?_⟩
  have hxV := hδball x (by
    calc dist (e x) (e x0) ≤ dist (e x) y + dist y (e x0) := dist_triangle _ _ _
      _ = dist y (e x) + dist y (e x0) := by rw [dist_comm (e x) y]
      _ < δ := by linarith [hxnear x0, hyd2])
  calc x = c.symm (c x) := (c.left_inv hxV.1).symm
    _ = c.symm (ψ y) := by rw [key x hxnear]
private theorem tubular_smoothRetraction_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] [SecondCountableTopology M]
    {n : ℕ}
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : IsSmoothEmbedding I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) e)
    (hclosed : IsClosed (Set.range e)) :
    ∃ (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
      (hU_sup : Set.range e ⊆ (U : Set (EuclideanSpace ℝ (Fin n)))),
      ∃ (r : ↥U → M),
        ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I (⊤ : ℕ∞) r ∧
          ∀ (x : M), r ⟨e x, hU_sup ⟨x, rfl⟩⟩ = x := by
  rcases isEmpty_or_nonempty M with hempty | hne
  · refine ⟨⊥, ?_, ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨x, -⟩ := hy
      exact (hempty.false x).elim
    · intro w
      have h0 : w.1 ∈ (∅ : Set (EuclideanSpace ℝ (Fin n))) := by
        rw [← TopologicalSpace.Opens.coe_bot]
        exact w.2
      exact (Set.notMem_empty _ h0).elim
    · intro w
      have h0 : w.1 ∈ (∅ : Set (EuclideanSpace ℝ (Fin n))) := by
        rw [← TopologicalSpace.Opens.coe_bot]
        exact w.2
      exact (Set.notMem_empty _ h0).elim
    · intro x
      exact (hempty.false x).elim
  · obtain ⟨x00⟩ := hne
    have hSne : (Set.range e).Nonempty := ⟨e x00, x00, rfl⟩
    have hnear : ∀ y : EuclideanSpace ℝ (Fin n), ∃ x : M,
        ∀ x' : M, dist y (e x) ≤ dist y (e x') := by
      intro y
      obtain ⟨s, hsS, hinf⟩ := hclosed.exists_infDist_eq_dist hSne y
      obtain ⟨x, rfl⟩ := hsS
      refine ⟨x, fun x' => ?_⟩
      rw [← hinf]
      exact Metric.infDist_le_dist_of_mem (Set.mem_range_self x')
    set R : EuclideanSpace ℝ (Fin n) → M :=
      fun y => Classical.choose (hnear y) with hRdef
    have hRspec : ∀ y x', dist y (e (R y)) ≤ dist y (e x') :=
      fun y => Classical.choose_spec (hnear y)
    have hloc : ∀ x0 : M, ∃ ε > 0, ∃ ψ : EuclideanSpace ℝ (Fin n) → E,
        ∀ y ∈ Metric.ball (e x0) ε, ψ y ∈ (extChartAt I x0).target ∧
          ContDiffAt ℝ (∞ : ℕ∞ω) ψ y ∧
          ∀ x : M, (∀ x' : M, dist y (e x) ≤ dist y (e x')) →
            x = (extChartAt I x0).symm (ψ y) :=
      fun x0 => local_nearest_point_structure e he x0
    choose ε hεpos ψ hψ using hloc
    set U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) :=
      ⟨⋃ x0, Metric.ball (e x0) (ε x0), isOpen_iUnion fun x0 => Metric.isOpen_ball⟩
      with hUdef
    have hU_sup : Set.range e ⊆ (U : Set (EuclideanSpace ℝ (Fin n))) := by
      intro y hy
      obtain ⟨x, rfl⟩ := hy
      change e x ∈ ⋃ x0, Metric.ball (e x0) (ε x0)
      exact Set.mem_iUnion.mpr ⟨x, Metric.mem_ball_self (hεpos x)⟩
    set r : ↥U → M := fun w => R w.1 with hrdef
    have hret : ∀ x : M, R (e x) = x := by
      intro x
      have h := hRspec (e x) x
      rw [dist_self] at h
      have h0 : dist (e x) (e (R (e x))) = 0 := le_antisymm h dist_nonneg
      have heq : e (R (e x)) = e x := by
        rw [← dist_eq_zero, dist_comm]
        exact h0
      exact he.isEmbedding.injective heq
    refine ⟨U, hU_sup, r, ?_, ?_⟩
    · intro w
      obtain ⟨x0, hx0⟩ := Set.mem_iUnion.mp w.2
      have hx0' : w.1 ∈ Metric.ball (e x0) (ε x0) := hx0
      have hlocw := hψ x0 w.1 hx0'
      obtain ⟨htar_mem, hψdiff, -⟩ := hlocw
      have htar : (extChartAt I x0).target ∈ 𝓝 (ψ x0 w.1) :=
        (isOpen_extChartAt_target x0).mem_nhds htar_mem
      have hcsym : ContMDiffAt 𝓘(ℝ, E) I (↑(⊤ : ℕ∞))
          ((extChartAt I x0).symm) (ψ x0 w.1) :=
        (contMDiffOn_extChartAt_symm x0).contMDiffAt htar
      have hψmd : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) (↑(⊤ : ℕ∞))
          (ψ x0) w.1 := hψdiff.contMDiffAt
      have hcomp : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I (↑(⊤ : ℕ∞))
          ((extChartAt I x0).symm ∘ ψ x0) w.1 :=
        hcsym.comp w.1 hψmd
      have hballmem : Metric.ball (e x0) (ε x0) ∈ 𝓝 w.1 :=
        Metric.isOpen_ball.mem_nhds hx0'
      have hRe : R =ᶠ[𝓝 w.1] ((extChartAt I x0).symm ∘ ψ x0) := by
        filter_upwards [hballmem] with z hz
        exact (hψ x0 z hz).2.2 (R z) (hRspec z)
      have hRmd : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I (↑(⊤ : ℕ∞)) R w.1 :=
        hcomp.congr_of_eventuallyEq hRe
      have hval : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (↑(⊤ : ℕ∞))
          (Subtype.val : ↥U → EuclideanSpace ℝ (Fin n)) w :=
        contMDiff_subtype_val.contMDiffAt
      change ContMDiffAt _ _ _ (R ∘ Subtype.val) w
      exact hRmd.comp w hval
    · intro x
      change R (e x) = x
      exact hret x


section
noncomputable section

open Manifold Topology
open scoped Manifold ContDiff

namespace MathlibExt.Geometry.Manifold.TubularNeighborhoodWanted

/--
**Smooth retraction onto a closed embedded manifold in $\mathbb{R}^n$.** Let $M$ be a Hausdorff,
second-countable smooth ($C^\infty$) manifold without boundary, modelled on a finite-dimensional
real normed space, and let $e \colon M \to \mathbb{R}^n$ be a smooth embedding (a $C^\infty$
immersion that is a topological embedding) whose image $e(M)$ is closed in $\mathbb{R}^n$. Then
there exist an open set $U \subseteq \mathbb{R}^n$ containing $e(M)$ and a $C^\infty$ map
$r \colon U \to M$ such that $r(e(x)) = x$ for every $x \in M$.

Proves `Wanted` entry `tubular_smoothRetraction`.

Source: Tubular neighborhood theorem; M. Hirsch,
Differential Topology; J. Lee, Introduction to Smooth Manifolds; Lean states smooth-retraction
corollary for closed embedding into `EuclideanSpace ℝ (Fin n)` via `Opens`.
-/
theorem tubular_smoothRetraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] [SecondCountableTopology M]
    {n : ℕ}
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : IsSmoothEmbedding I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) e)
    (hclosed : IsClosed (Set.range e)) :
    ∃ (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
      (hU_sup : Set.range e ⊆ (U : Set (EuclideanSpace ℝ (Fin n)))),
      ∃ (r : ↥U → M),
        ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I (⊤ : ℕ∞) r ∧
          ∀ (x : M), r ⟨e x, hU_sup ⟨x, rfl⟩⟩ = x := by
  exact tubular_smoothRetraction_aux e he hclosed

end MathlibExt.Geometry.Manifold.TubularNeighborhoodWanted
end
end
