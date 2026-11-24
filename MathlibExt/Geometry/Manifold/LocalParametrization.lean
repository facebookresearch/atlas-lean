/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Immersion

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import MathlibExt.Geometry.Manifold.LocalGraph

/-!
# Local parametrizations of regular level sets

This file proves that a regular level set of a continuously differentiable map between
Euclidean spaces is locally the image of a global continuously differentiable immersion.
It also proves that the graph of a continuously differentiable map is an immersion.
-/

@[expose] public section

open scoped Topology Manifold ContDiff
open Manifold

noncomputable section

namespace MathlibExt.Geometry.Manifold.LocalParametrizationWanted

private def levelParam_graphDiffeomorph
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : ℕ∞ω} (h : E → F) (hh : ContDiff ℝ n h) (e : (E × F) ≃L[ℝ] G) :
    Diffeomorph 𝓘(ℝ, G) 𝓘(ℝ, G) G G n where
  toEquiv := {
    toFun := fun z => e ((e.symm z).1, (e.symm z).2 - h (e.symm z).1)
    invFun := fun z => e ((e.symm z).1, (e.symm z).2 + h (e.symm z).1)
    left_inv := by
      intro z
      simp
    right_inv := by
      intro z
      simp }
  contMDiff_toFun := contMDiff_iff_contDiff.mpr <| by
    have ha : ContDiff ℝ n (fun z : G => (e.symm z).1) :=
      contDiff_fst.comp e.symm.contDiff
    have hb : ContDiff ℝ n (fun z : G => (e.symm z).2) :=
      contDiff_snd.comp e.symm.contDiff
    exact e.contDiff.comp (ha.prodMk (hb.sub (hh.comp ha)))
  contMDiff_invFun := contMDiff_iff_contDiff.mpr <| by
    have ha : ContDiff ℝ n (fun z : G => (e.symm z).1) :=
      contDiff_fst.comp e.symm.contDiff
    have hb : ContDiff ℝ n (fun z : G => (e.symm z).2) :=
      contDiff_snd.comp e.symm.contDiff
    exact e.contDiff.comp (ha.prodMk (hb.add (hh.comp ha)))

private theorem levelParam_isImmersion_equiv_graph
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : ℕ∞ω} (h : E → F) (hh : ContDiff ℝ n h) (e : (E × F) ≃L[ℝ] G) :
    IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, G) n (fun x => e (x, h x)) := by
  let q := levelParam_graphDiffeomorph h hh e
  have hq : q.toHomeomorph.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℝ, G) n G := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · simpa using q.contMDiff.contMDiffOn
    · simpa using q.symm.contMDiff.contMDiffOn
  apply (show IsImmersionOfComplement F 𝓘(ℝ, E) 𝓘(ℝ, G) n
      (fun x => e (x, h x)) from ?_).isImmersion
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (e.contDiff.comp (contDiff_id.prodMk hh)).continuous.continuousAt
    e (chartAt E x) q.toHomeomorph.toOpenPartialHomeomorph
    (mem_chart_source E x) (by simp)
    (IsManifold.chart_mem_maximalAtlas x) hq
  intro y hy
  change e ((e.symm (e (y, h y))).1,
    (e.symm (e (y, h y))).2 - h (e.symm (e (y, h y))).1) = e (y, 0)
  simp

/-- **Graph maps are immersions.** Let $E$ and $F$ be real normed spaces, let
$n \in \mathbb{N} \cup \{\infty, \omega\}$ and let $h \colon E \to F$ be a $C^n$ map. Then the
graph map $x \mapsto (x, h(x))$ from $E$ to $E \times F$ is a $C^n$ immersion, where $E$ and
$E \times F$ are regarded as manifolds modelled on themselves. -/
theorem _root_.ContDiff.isImmersion_graph
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞ω} {h : E → F} (hh : ContDiff ℝ n h) :
    IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, E × F) n (fun x => (x, h x)) := by
  simpa using levelParam_isImmersion_equiv_graph h hh
    (ContinuousLinearEquiv.refl ℝ (E × F))

private theorem levelParam_exists_contDiff_extension
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {x : E} {g : E → F}
    (hs : s ∈ 𝓝 x) (hg : ContDiffOn ℝ 1 g s) :
    ∃ U : Set E, IsOpen U ∧ U ∈ 𝓝 x ∧ U ⊆ s ∧
      ∃ h : E → F, ContDiff ℝ 1 h ∧ Set.EqOn h g U := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hs
  let χ : ContDiffBump x := {
    rIn := r / 3
    rOut := (2 * r) / 3
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  let h : E → F := fun y => χ y • g y
  have hh_ball : ContDiffOn ℝ 1 h (Metric.ball x r) := by
    exact χ.contDiff.contDiffOn.smul (hg.mono hball)
  have hh_out : ContDiffOn ℝ 1 h ((Metric.closedBall x χ.rOut)ᶜ) := by
    have hz : ContDiffOn ℝ 1 (fun _ : E => (0 : F))
        ((Metric.closedBall x χ.rOut)ᶜ) := contDiffOn_const
    apply hz.congr
    intro y hy
    have hdist : χ.rOut ≤ dist y x := by
      simp only [Set.mem_compl_iff, Metric.mem_closedBall] at hy
      exact le_of_not_ge hy
    simp [h, χ.zero_of_le_dist hdist]
  have hcover : Metric.ball x r ∪ (Metric.closedBall x χ.rOut)ᶜ = Set.univ := by
    have hout : χ.rOut < r := by
      dsimp [χ]
      linarith
    have hclosed : Metric.closedBall x χ.rOut ⊆ Metric.ball x r :=
      Metric.closedBall_subset_ball hout
    ext y
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
    by_cases hy : y ∈ Metric.closedBall x χ.rOut
    · exact Or.inl (hclosed hy)
    · exact Or.inr hy
  have hh : ContDiff ℝ 1 h := contDiff_of_contDiffOn_union_of_isOpen
    hh_ball hh_out hcover Metric.isOpen_ball Metric.isClosed_closedBall.isOpen_compl
  refine ⟨Metric.ball x χ.rIn, Metric.isOpen_ball, Metric.ball_mem_nhds x χ.rIn_pos,
    (Metric.ball_subset_ball ?_).trans hball, h, hh, ?_⟩
  · dsimp [χ]
    linarith
  intro y hy
  have hy' : y ∈ Metric.closedBall x χ.rIn := Metric.ball_subset_closedBall hy
  simp [h, χ.one_of_mem_closedBall hy']

private theorem levelParam_image_eq
    {E G F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] G × F) {g h : G → F} {U₀ U : Set G} {V S : Set E}
    (hU : U ⊆ U₀) (heq : Set.EqOn h g U)
    (hgraph : V ∩ S = V ∩ e ⁻¹' {p : G × F | p.1 ∈ U₀ ∧ p.2 = g p.1}) :
    (fun u => e.symm (u, h u)) ''
        (U ∩ (fun u => e.symm (u, h u)) ⁻¹'
          (V ∩ e ⁻¹' {p : G × F | p.1 ∈ U})) =
      (V ∩ e ⁻¹' {p : G × F | p.1 ∈ U}) ∩ S := by
  ext x
  constructor
  · rintro ⟨u, ⟨hu, huV⟩, rfl⟩
    refine ⟨huV, ?_⟩
    have hmem : e.symm (u, h u) ∈
        V ∩ e ⁻¹' {p : G × F | p.1 ∈ U₀ ∧ p.2 = g p.1} := by
      refine ⟨huV.1, ?_⟩
      simpa using ⟨hU hu, heq hu⟩
    have hlevel : e.symm (u, h u) ∈ V ∩ S := by
      rw [hgraph]
      exact hmem
    exact hlevel.2
  · rintro ⟨hxW, hxS⟩
    have hxgraph : x ∈ V ∩ e ⁻¹' {p : G × F |
        p.1 ∈ U₀ ∧ p.2 = g p.1} := by
      rw [← hgraph]
      exact ⟨hxW.1, hxS⟩
    let u := (e x).1
    have hu : u ∈ U := hxW.2
    have hφx : e.symm (u, h u) = x := by
      apply e.injective
      rw [e.apply_symm_apply]
      apply Prod.ext
      · rfl
      · exact (heq hu).trans hxgraph.2.2.symm
    refine ⟨u, ⟨hu, ?_⟩, hφx⟩
    change e.symm (u, h u) ∈ V ∩ e ⁻¹' {p : G × F | p.1 ∈ U}
    rw [hφx]
    exact hxW

/--
**Regular level sets are locally parametrized by immersions.** Let
$f \colon \mathbb{R}^{k+m} \to \mathbb{R}^m$ be a $C^1$ map and let $x_0 \in \mathbb{R}^{k+m}$ be a
point at which the derivative $Df(x_0)$ is surjective. Then there exist an open set
$U \subseteq \mathbb{R}^k$, a point $u_0 \in U$, a map $\varphi \colon \mathbb{R}^k \to
\mathbb{R}^{k+m}$ that is $C^1$ and a $C^1$ immersion on all of $\mathbb{R}^k$, and a
neighbourhood $V$ of $x_0$ such that $\varphi(u_0) = x_0$ and
$\varphi(U \cap \varphi^{-1}(V)) = V \cap f^{-1}(f(x_0))$.

Proves `Wanted` entry `regularLevelSet_localParametrization`.

Proof: Apply the implicit function theorem in adapted linear coordinates, then use a smooth bump
to extend the local graphing function globally. A shear chart makes its graph map an immersion.

Sources: undergrad.yaml
`Submanifolds of R^n / local parameterization` (missing); J. Lee, Introduction to Smooth
Manifolds, 2nd ed., Ch. 4 (rank theorem).
-/
theorem regularLevelSet_localParametrization
    {k m : ℕ}
    (f : EuclideanSpace ℝ (Fin (k + m)) → EuclideanSpace ℝ (Fin m))
    (hf : ContDiff ℝ 1 f) (x₀ : EuclideanSpace ℝ (Fin (k + m)))
    (hreg : Function.Surjective (fderiv ℝ f x₀)) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin k))) (_ : IsOpen U)
      (u₀ : EuclideanSpace ℝ (Fin k)) (_ : u₀ ∈ U)
      (φ : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin (k + m))),
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (k + m))) 1 φ ∧
      IsImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (k + m))) 1 φ ∧
      ∃ V ∈ 𝓝 x₀, φ '' (U ∩ φ ⁻¹' V) = V ∩ f ⁻¹' {f x₀} ∧ φ u₀ = x₀ := by
  obtain ⟨e, U₀, hU₀, g, hg, V₀, hV₀, hgraph⟩ :=
    ContDiff.exists_localGraph_of_surjective_fderiv
      (E := EuclideanSpace ℝ (Fin (k + m)))
      (G := EuclideanSpace ℝ (Fin k))
      (F := EuclideanSpace ℝ (Fin m))
      (by simp only [finrank_euclideanSpace_fin]) f hf x₀ hreg
  obtain ⟨U, hUopen, hUnhds, hUsub, h, hh, hhg⟩ :=
    levelParam_exists_contDiff_extension hU₀ hg
  let u₀ := (e x₀).1
  let φ := fun u => e.symm (u, h u)
  let V := V₀ ∩ e ⁻¹'
    {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) | p.1 ∈ U}
  have hu₀ : u₀ ∈ U := by
    exact mem_of_mem_nhds hUnhds
  have hV : V ∈ 𝓝 x₀ := by
    apply Filter.inter_mem hV₀
    change (Prod.fst ∘ e) ⁻¹' U ∈ 𝓝 x₀
    exact (continuous_fst.comp e.continuous).continuousAt.preimage_mem_nhds hUnhds
  have hx₀graph : x₀ ∈ V₀ ∩ e ⁻¹'
      {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) |
        p.1 ∈ U₀ ∧ p.2 = g p.1} := by
    rw [← hgraph]
    exact ⟨mem_of_mem_nhds hV₀, by simp⟩
  have hφu₀ : φ u₀ = x₀ := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext
    · rfl
    · exact (hhg hu₀).trans hx₀graph.2.2.symm
  have hφdiff : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (k + m))) 1 φ := by
    apply contMDiff_iff_contDiff.mpr
    exact e.symm.contDiff.comp (contDiff_id.prodMk hh)
  have hφimm : IsImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (k + m))) 1 φ := by
    exact levelParam_isImmersion_equiv_graph h hh e.symm
  have himage : φ '' (U ∩ φ ⁻¹' V) = V ∩ f ⁻¹' {f x₀} := by
    simpa [φ, V] using levelParam_image_eq e hUsub hhg hgraph
  exact ⟨U, hUopen, u₀, hu₀, φ, hφdiff, hφimm, V, hV, himage, hφu₀⟩

end MathlibExt.Geometry.Manifold.LocalParametrizationWanted
