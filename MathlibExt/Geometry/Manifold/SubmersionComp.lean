/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.Submersion

-- `IsSubmersionOfComplement` is not `@[expose]` at this Mathlib pin (unlike
-- `IsImmersionOfComplement`), and `IsSubmersionOfComplement.comp` must unfold it.
import all Mathlib.Geometry.Manifold.Submersion

/-! # Composition of submersions

This file proves that pointwise and global submersions between boundaryless Banach manifolds are
closed under composition. The proof composes their local projection normal forms after aligning
the intermediate charts.
-/

@[expose] public section

open scoped Topology ContDiff
open Manifold

noncomputable section

namespace MathlibExt.Geometry.Manifold.SubmersionCompWanted

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E'' : Type u} {E''' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G}
  {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}

private def submersionCompExtend [I.Boundaryless] (φ : OpenPartialHomeomorph M H) :
    OpenPartialHomeomorph M E where
  toPartialEquiv := φ.extend I
  continuousOn_toFun := φ.continuousOn_extend
  continuousOn_invFun := φ.continuousOn_extend_symm
  open_source := φ.isOpen_extend_source
  open_target := φ.isOpen_extend_target

private def submersionCompEquiv {F₁ F₂ : Type u}
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (e₁ : E ≃L[𝕜] (E'' × F₁)) (e₂ : E'' ≃L[𝕜] (E''' × F₂)) :
    E ≃L[𝕜] (E''' × (F₂ × F₁)) :=
  e₁.trans <| (e₂.prodCongr <| ContinuousLinearEquiv.refl 𝕜 F₁).trans <|
    ContinuousLinearEquiv.prodAssoc 𝕜 E''' F₂ F₁

private def submersionCompCoordChange [J.Boundaryless]
    (φ ψ : OpenPartialHomeomorph N G) : OpenPartialHomeomorph E'' E'' :=
  (submersionCompExtend (I := J) φ).symm.trans (submersionCompExtend (I := J) ψ)

private lemma submersionCompCoordChange_contDiffOn [J.Boundaryless]
    {φ ψ : OpenPartialHomeomorph N G}
    (hφ : φ ∈ IsManifold.maximalAtlas J n N)
    (hψ : ψ ∈ IsManifold.maximalAtlas J n N) :
    ContDiffOn 𝕜 n (submersionCompCoordChange (J := J) φ ψ)
      (submersionCompCoordChange (J := J) φ ψ).source := by
  exact J.contDiffOn_extendCoordChange hφ hψ

private lemma submersionCompCoordChange_contDiffOn_symm [J.Boundaryless]
    {φ ψ : OpenPartialHomeomorph N G}
    (hφ : φ ∈ IsManifold.maximalAtlas J n N)
    (hψ : ψ ∈ IsManifold.maximalAtlas J n N) :
    ContDiffOn 𝕜 n (submersionCompCoordChange (J := J) φ ψ).symm
      (submersionCompCoordChange (J := J) φ ψ).target := by
  exact J.contDiffOn_extendCoordChange_symm hφ hψ

private def submersionCompLiftModel [J.Boundaryless]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] (E'' × F)) (φ ψ : OpenPartialHomeomorph N G) :
    OpenPartialHomeomorph E E :=
  (e.toHomeomorph.toOpenPartialHomeomorph.trans
      ((submersionCompCoordChange (J := J) φ ψ).prod
        (OpenPartialHomeomorph.refl F))).trans
    e.symm.toHomeomorph.toOpenPartialHomeomorph

private def submersionCompLift [I.Boundaryless] [J.Boundaryless]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] (E'' × F)) (φ ψ : OpenPartialHomeomorph N G) :
    OpenPartialHomeomorph H H :=
  (I.toHomeomorph.toOpenPartialHomeomorph.trans
    (submersionCompLiftModel (J := J) e φ ψ)).trans
    I.toHomeomorph.symm.toOpenPartialHomeomorph

private lemma submersionCompLiftModel_contDiffOn [J.Boundaryless]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] (E'' × F)) {φ ψ : OpenPartialHomeomorph N G}
    (hφ : φ ∈ IsManifold.maximalAtlas J n N)
    (hψ : ψ ∈ IsManifold.maximalAtlas J n N) :
    ContDiffOn 𝕜 n (submersionCompLiftModel (J := J) e φ ψ)
      (submersionCompLiftModel (J := J) e φ ψ).source := by
  let θ := submersionCompCoordChange (J := J) φ ψ
  have hθ : ContDiffOn 𝕜 n θ θ.source := submersionCompCoordChange_contDiffOn hφ hψ
  have hp : ContDiffOn 𝕜 n (Prod.map θ (id : F → F)) (θ.source ×ˢ Set.univ) :=
    hθ.prodMap contDiff_id.contDiffOn
  have hpe := hp.comp e.contDiff.contDiffOn (Set.mapsTo_preimage _ _)
  have h := e.symm.contDiff.contDiffOn.comp hpe (Set.mapsTo_univ _ _)
  simpa [submersionCompLiftModel, θ, Function.comp_def, Prod.map,
    OpenPartialHomeomorph.trans_source] using h

private lemma submersionCompLiftModel_contDiffOn_symm [J.Boundaryless]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] (E'' × F)) {φ ψ : OpenPartialHomeomorph N G}
    (hφ : φ ∈ IsManifold.maximalAtlas J n N)
    (hψ : ψ ∈ IsManifold.maximalAtlas J n N) :
    ContDiffOn 𝕜 n (submersionCompLiftModel (J := J) e φ ψ).symm
      (submersionCompLiftModel (J := J) e φ ψ).target := by
  let θ := submersionCompCoordChange (J := J) φ ψ
  have hθ : ContDiffOn 𝕜 n θ.symm θ.target :=
    submersionCompCoordChange_contDiffOn_symm hφ hψ
  have hp : ContDiffOn 𝕜 n (Prod.map θ.symm (id : F → F)) (θ.target ×ˢ Set.univ) :=
    hθ.prodMap contDiff_id.contDiffOn
  have hpe := hp.comp e.contDiff.contDiffOn (Set.mapsTo_preimage _ _)
  have h := e.symm.contDiff.contDiffOn.comp hpe (Set.mapsTo_univ _ _)
  simpa [submersionCompLiftModel, θ, Function.comp_def, Prod.map,
    OpenPartialHomeomorph.trans_target] using h

private lemma submersionCompLift_mem_contDiffGroupoid [I.Boundaryless] [J.Boundaryless]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] (E'' × F)) {φ ψ : OpenPartialHomeomorph N G}
    (hφ : φ ∈ IsManifold.maximalAtlas J n N)
    (hψ : ψ ∈ IsManifold.maximalAtlas J n N) :
    submersionCompLift (I := I) (J := J) e φ ψ ∈ contDiffGroupoid n I := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  have hpre (s : Set E) : I.symm ⁻¹' I ⁻¹' s = s := by
    ext z
    simp only [Set.mem_preimage]
    rw [I.right_inv]
    simp [I.range_eq_univ]
  have hpre' (s : Set E) : I.symm ⁻¹' (I.toHomeomorph : H → E) ⁻¹' s = s := by
    change I.symm ⁻¹' I ⁻¹' s = s
    exact hpre s
  constructor
  · simpa [submersionCompLift, Function.comp_def, I.range_eq_univ,
      OpenPartialHomeomorph.trans_source, hpre'] using
      submersionCompLiftModel_contDiffOn (J := J) e hφ hψ
  · simpa [submersionCompLift, Function.comp_def, I.range_eq_univ,
      OpenPartialHomeomorph.trans_target, hpre'] using
      submersionCompLiftModel_contDiffOn_symm (J := J) e hφ hψ

private def submersionCompDomChart [I.Boundaryless] [J.Boundaryless]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : M → N} {x : M} (hf : IsSubmersionAtOfComplement F I J n f x)
    (ψ : OpenPartialHomeomorph N G) : OpenPartialHomeomorph M H :=
  hf.domChart.trans <| submersionCompLift (I := I) (J := J) hf.equiv hf.codChart ψ

private lemma submersionCompDomChart_mem_maximalAtlas [I.Boundaryless] [J.Boundaryless]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : M → N} {x : M} (hf : IsSubmersionAtOfComplement F I J n f x)
    {ψ : OpenPartialHomeomorph N G} (hψ : ψ ∈ IsManifold.maximalAtlas J n N) :
    submersionCompDomChart hf ψ ∈ IsManifold.maximalAtlas I n M := by
  change submersionCompDomChart hf ψ ∈ (contDiffGroupoid n I).maximalAtlas M
  rw [mem_maximalAtlas_iff]
  intro c hc
  have hdom : hf.domChart ∈ (contDiffGroupoid n I).maximalAtlas M :=
    hf.domChart_mem_maximalAtlas
  have hcompat := mem_maximalAtlas_iff.mp hdom c hc
  have hL := submersionCompLift_mem_contDiffGroupoid
    (I := I) (J := J) hf.equiv hf.codChart_mem_maximalAtlas hψ
  constructor
  · rw [submersionCompDomChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid n I).trans ((contDiffGroupoid n I).symm hL) hcompat.1
  · rw [submersionCompDomChart, ← OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid n I).trans hcompat.2 hL

private lemma submersionCompEquiv_fst_eq [I.Boundaryless]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : M → N} {x y : M} (hf : IsSubmersionAtOfComplement F I J n f x)
    (hy : y ∈ hf.domChart.source) :
    (hf.equiv (hf.domChart.extend I y)).1 = hf.codChart.extend J (f y) := by
  have hz : hf.domChart.extend I y ∈ (hf.domChart.extend I).target :=
    (hf.domChart.extend I).map_source (by simpa using hy)
  have hw := hf.writtenInCharts hz
  rw [Function.comp_apply, Function.comp_apply,
    hf.domChart.extend_left_inv (I := I) hy] at hw
  exact hw.symm

private lemma submersionComp_mem_domChart_source [I.Boundaryless] [J.Boundaryless]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : M → N} {x y : M} (hf : IsSubmersionAtOfComplement F I J n f x)
    (ψ : OpenPartialHomeomorph N G) :
    y ∈ (submersionCompDomChart hf ψ).source ↔
      y ∈ hf.domChart.source ∧ f y ∈ ψ.source := by
  rw [submersionCompDomChart, OpenPartialHomeomorph.trans_source]
  refine and_congr_right fun hy ↦ ?_
  have hcoord : (hf.equiv (I (hf.domChart y))).1 = hf.codChart.extend J (f y) :=
    submersionCompEquiv_fst_eq hf hy
  simp only [submersionCompLift, submersionCompLiftModel, submersionCompCoordChange,
    submersionCompExtend, OpenPartialHomeomorph.extend,
    ContinuousLinearEquiv.toHomeomorph_symm, Homeomorph.symm_toOpenPartialHomeomorph,
    OpenPartialHomeomorph.trans_toPartialEquiv, OpenPartialHomeomorph.prod_toPartialHomeomorph,
    OpenPartialHomeomorph.symm_toPartialEquiv, OpenPartialHomeomorph.refl_partialEquiv,
    PartialEquiv.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    PartialHomeomorph.toFun_eq_coe, OpenPartialHomeomorph.coe_toPartialHomeomorph,
    Homeomorph.toOpenPartialHomeomorph_apply, ContinuousLinearEquiv.coe_toHomeomorph,
    PartialEquiv.prod_source, PartialEquiv.symm_source, PartialEquiv.trans_target,
    ModelWithCorners.target_eq, ModelWithCorners.toPartialEquiv_coe_symm,
    PartialEquiv.coe_trans_symm, PartialHomeomorph.coe_toPartialEquiv_symm,
    OpenPartialHomeomorph.coe_toPartialHomeomorph_symm, ModelWithCorners.source_eq,
    Set.preimage_univ, Set.inter_univ, PartialEquiv.refl_source, Set.univ_inter,
    PartialEquiv.coe_trans, PartialEquiv.prod_coe, ModelWithCorners.toPartialEquiv_coe,
    Function.comp_apply, PartialEquiv.refl_coe, id_eq,
    Homeomorph.toOpenPartialHomeomorph_target,
    Homeomorph.toOpenPartialHomeomorph_symm_apply,
    ContinuousLinearEquiv.coe_symm_toHomeomorph, Set.mem_preimage,
    ModelWithCorners.toHomeomorph_apply, Set.mem_prod, Set.mem_inter_iff, Set.mem_range,
    Set.mem_univ, and_true]
  rw [hcoord]
  have hfy : f y ∈ hf.codChart.source := hf.source_subset_preimage_source hy
  simp [hf.codChart.map_source hfy, hf.codChart.left_inv hfy]

private lemma submersionComp_writtenInCharts [I.Boundaryless] [J.Boundaryless]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : M → N} {x : M} (hf : IsSubmersionAtOfComplement F I J n f x)
    (ψ : OpenPartialHomeomorph N G) :
    Set.EqOn ((ψ.extend J) ∘ f ∘ ((submersionCompDomChart hf ψ).extend I).symm)
      (Prod.fst ∘ hf.equiv) ((submersionCompDomChart hf ψ).extend I).target := by
  intro z hz
  rw [OpenPartialHomeomorph.extend_target_eq_image_source] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hy' := (submersionComp_mem_domChart_source hf ψ).mp hy
  have hfy : f y ∈ hf.codChart.source := hf.source_subset_preimage_source hy'.1
  have hcoord : (hf.equiv (I (hf.domChart y))).1 = hf.codChart.extend J (f y) :=
    submersionCompEquiv_fst_eq hf hy'.1
  rw [Function.comp_apply, Function.comp_apply,
    (submersionCompDomChart hf ψ).extend_left_inv (I := I) hy]
  simp only [OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, PartialHomeomorph.toFun_eq_coe,
    OpenPartialHomeomorph.coe_toPartialHomeomorph, Function.comp_apply,
    submersionCompDomChart, submersionCompLift, submersionCompLiftModel,
    submersionCompCoordChange, submersionCompExtend,
    ContinuousLinearEquiv.toHomeomorph_symm, Homeomorph.symm_toOpenPartialHomeomorph,
    OpenPartialHomeomorph.trans_toPartialEquiv, OpenPartialHomeomorph.prod_toPartialHomeomorph,
    OpenPartialHomeomorph.symm_toPartialEquiv, OpenPartialHomeomorph.refl_partialEquiv,
    PartialHomeomorph.coe_toPartialEquiv_symm,
    OpenPartialHomeomorph.coe_toPartialHomeomorph_symm,
    Homeomorph.toOpenPartialHomeomorph_symm_apply,
    ContinuousLinearEquiv.coe_symm_toHomeomorph, PartialEquiv.prod_coe,
    PartialEquiv.coe_trans_symm, ModelWithCorners.toPartialEquiv_coe_symm,
    PartialEquiv.refl_coe, id_eq, Homeomorph.toOpenPartialHomeomorph_apply,
    ContinuousLinearEquiv.coe_toHomeomorph, ModelWithCorners.toHomeomorph_apply, hcoord,
    ModelWithCorners.left_inv, hfy, OpenPartialHomeomorph.left_inv,
    ModelWithCorners.toHomeomorph_symm_apply]
  rw [I.right_inv (by simp [I.range_eq_univ])]
  simp

/-- **Changing the target chart of a submersion at a point.** Let $\mathbb{K}$ be a nontrivially
normed field, let $n \in \mathbb{N} \cup \{\infty, \omega\}$, and let $M$ and $N$ be charted spaces
modelled, through models with corners, on normed spaces $E$ and $E''$ over $\mathbb{K}$, both
models without boundary. Let $f : M \to N$ be a $C^n$ submersion at $x \in M$ with complement $F$,
and let $e : E \to E'' \times F$ be the continuous linear equivalence chosen for it. Then for every
chart $\psi$ of $N$ in the $C^n$ maximal atlas with $f(x)$ in its domain there is a chart
$\varphi$ of $M$ in the $C^n$ maximal atlas with $x$ in its domain, such that $f$ maps the domain
of $\varphi$ into the domain of $\psi$ and
$\hat\psi \circ f \circ \hat\varphi^{-1} = \mathrm{pr}_1 \circ e$ on the image of $\hat\varphi$,
where $\hat\varphi$ and $\hat\psi$ denote the charts followed by the models with corners.

Here $f$ is a $C^n$ submersion at $x$ with complement $F$ (a normed space over $\mathbb{K}$) when
there are charts of $M$ around $x$ and of $N$ around $f(x)$ in the $C^n$ maximal atlases, the
first mapped by $f$ into the second, in which $f$ reads $\mathrm{pr}_1 \circ e$ on the image of
the first, for some continuous linear equivalence $e : E \to E'' \times F$; a witness of this
fixes one such $e$. -/
theorem _root_.Manifold.IsSubmersionAtOfComplement.exists_domChart_of_codChart
    [I.Boundaryless] [J.Boundaryless]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : M → N} {x : M} (hf : IsSubmersionAtOfComplement F I J n f x)
    (codChart : OpenPartialHomeomorph N G) (hfx : f x ∈ codChart.source)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N) :
    ∃ domChart : OpenPartialHomeomorph M H,
      x ∈ domChart.source ∧
      domChart ∈ IsManifold.maximalAtlas I n M ∧
      domChart.source ⊆ f ⁻¹' codChart.source ∧
      Set.EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm)
        (Prod.fst ∘ hf.equiv) (domChart.extend I).target := by
  refine ⟨submersionCompDomChart hf codChart, ?_, ?_, ?_, ?_⟩
  · exact (submersionComp_mem_domChart_source hf codChart).2
      ⟨hf.mem_domChart_source, hfx⟩
  · exact submersionCompDomChart_mem_maximalAtlas hf hcodChart
  · intro y hy
    exact (submersionComp_mem_domChart_source hf codChart).1 hy |>.2
  · exact submersionComp_writtenInCharts hf codChart

set_option maxHeartbeats 800000 in
-- Elaborating the composed chart normal form needs more than the default heartbeat budget.
/-- **Composition of submersions at a point with chosen complements.** Let $\mathbb{K}$ be a
nontrivially normed field, let $n \in \mathbb{N} \cup \{\infty, \omega\}$, and let $M$, $N$, $N'$
be charted spaces modelled, through models with corners, on normed spaces $E$, $E''$, $E'''$ over
$\mathbb{K}$, where the models of $M$ and $N$ have no boundary. Let $F_1$ and $F_2$ be normed
spaces over $\mathbb{K}$. If $f : M \to N$ is a $C^n$ submersion at $x \in M$ with complement
$F_1$ and $g : N \to N'$ is a $C^n$ submersion at $f(x)$ with complement $F_2$, then
$g \circ f$ is a $C^n$ submersion at $x$ with complement $F_2 \times F_1$.

Here $f$ is a $C^n$ submersion at $x$ with complement $F$ when there are charts $\varphi$ of $M$
around $x$ and $\psi$ of $N$ around $f(x)$ in the $C^n$ maximal atlases, with $f$ mapping the
domain of $\varphi$ into the domain of $\psi$, and a continuous linear equivalence
$e : E \to E'' \times F$ such that
$\hat\psi \circ f \circ \hat\varphi^{-1} = \mathrm{pr}_1 \circ e$ on the image of $\hat\varphi$,
where $\hat\varphi$ and $\hat\psi$ denote the charts followed by the models with corners. -/
theorem _root_.Manifold.IsSubmersionAtOfComplement.comp
    [I.Boundaryless] [J.Boundaryless]
    {F₁ F₂ : Type u}
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    {f : M → N} {g : N → N'} {x : M}
    (hg : IsSubmersionAtOfComplement F₂ J J' n g (f x))
    (hf : IsSubmersionAtOfComplement F₁ I J n f x) :
    IsSubmersionAtOfComplement (F₂ × F₁) I J' n (g ∘ f) x := by
  obtain ⟨domChart, hx, hdomChart, hsource, hfwritten⟩ :=
    hf.exists_domChart_of_codChart hg.domChart hg.mem_domChart_source
      hg.domChart_mem_maximalAtlas
  apply IsSubmersionAtOfComplement.mk_of_charts (submersionCompEquiv hf.equiv hg.equiv)
    domChart hg.codChart hx hg.mem_codChart_source hdomChart hg.codChart_mem_maximalAtlas
  · intro y hy
    exact hg.source_subset_preimage_source (hsource hy)
  · intro z hz
    have hy : (domChart.extend I).symm z ∈ domChart.source := by
      have := (domChart.extend I).map_target hz
      simpa using this
    have hfy : f ((domChart.extend I).symm z) ∈ hg.domChart.source := hsource hy
    have hfw := hfwritten hz
    simp only [Function.comp_apply] at hfw
    have hez : (hf.equiv z).1 ∈ (hg.domChart.extend J).target := by
      rw [← hfw]
      exact (hg.domChart.extend J).map_source (by simpa using hfy)
    have hgw := hg.writtenInCharts hez
    simp only [Function.comp_apply] at hgw
    conv_lhs at hgw =>
      rw [← hfw, hg.domChart.extend_left_inv (I := J) hfy]
    change hg.codChart.extend J' (g (f ((domChart.extend I).symm z))) =
      (hg.equiv (hf.equiv z).1).1
    exact hgw

/-- **Submersions at a point are closed under composition.** Let $\mathbb{K}$ be a nontrivially
normed field, let $n \in \mathbb{N} \cup \{\infty, \omega\}$, and let $M$, $N$, $N'$ be charted
spaces modelled, through models with corners, on normed spaces $E$, $E''$, $E'''$ over
$\mathbb{K}$, where the models of $M$ and $N$ have no boundary. If $f : M \to N$ is a $C^n$
submersion at $x \in M$ and $g : N \to N'$ is a $C^n$ submersion at $f(x)$, then $g \circ f$ is a
$C^n$ submersion at $x$.

Here $f$ is a $C^n$ submersion at $x$ when, for some normed space $F$ over $\mathbb{K}$, there are
charts $\varphi$ of $M$ around $x$ and $\psi$ of $N$ around $f(x)$ in the $C^n$ maximal atlases,
with $f$ mapping the domain of $\varphi$ into the domain of $\psi$, and a continuous linear
equivalence $e : E \to E'' \times F$ such that
$\hat\psi \circ f \circ \hat\varphi^{-1} = \mathrm{pr}_1 \circ e$ on the image of $\hat\varphi$,
where $\hat\varphi$ and $\hat\psi$ denote the charts followed by the models with corners. -/
theorem _root_.Manifold.IsSubmersionAt.comp
    [I.Boundaryless] [J.Boundaryless]
    {f : M → N} {g : N → N'} {x : M}
    (hg : IsSubmersionAt J J' n g (f x)) (hf : IsSubmersionAt I J n f x) :
    IsSubmersionAt I J' n (g ∘ f) x := by
  exact (hg.isSubmersionAtOfComplement_complement.comp
    hf.isSubmersionAtOfComplement_complement).isSubmersionAt

/-- **Composition of submersions with chosen complements.** Let $\mathbb{K}$ be a nontrivially
normed field, let $n \in \mathbb{N} \cup \{\infty, \omega\}$, and let $M$, $N$, $N'$ be charted
spaces modelled, through models with corners, on normed spaces $E$, $E''$, $E'''$ over
$\mathbb{K}$, where the models of $M$ and $N$ have no boundary. Let $F_1$ and $F_2$ be normed
spaces over $\mathbb{K}$. If $f : M \to N$ is a $C^n$ submersion with complement $F_1$ and
$g : N \to N'$ is a $C^n$ submersion with complement $F_2$, then $g \circ f$ is a $C^n$
submersion with complement $F_2 \times F_1$.

Here $f$ is a $C^n$ submersion with complement $F$ when at every $x \in M$ there are charts
$\varphi$ of $M$ around $x$ and $\psi$ of $N$ around $f(x)$ in the $C^n$ maximal atlases, with
$f$ mapping the domain of $\varphi$ into the domain of $\psi$, and a continuous linear
equivalence $e : E \to E'' \times F$ such that
$\hat\psi \circ f \circ \hat\varphi^{-1} = \mathrm{pr}_1 \circ e$ on the image of $\hat\varphi$,
where $\hat\varphi$ and $\hat\psi$ denote the charts followed by the models with corners. -/
theorem _root_.Manifold.IsSubmersionOfComplement.comp
    [I.Boundaryless] [J.Boundaryless]
    {F₁ F₂ : Type u}
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    {f : M → N} {g : N → N'}
    (hg : IsSubmersionOfComplement F₂ J J' n g)
    (hf : IsSubmersionOfComplement F₁ I J n f) :
    IsSubmersionOfComplement (F₂ × F₁) I J' n (g ∘ f) :=
  fun x ↦ (hg (f x)).comp (hf x)

/-- **Submersions are closed under composition.** Let $\mathbb{K}$ be a nontrivially normed
field, let $n \in \mathbb{N} \cup \{\infty, \omega\}$, and let $M$, $N$, $N'$ be charted spaces
modelled, through models with corners, on normed spaces $E$, $E''$, $E'''$ over $\mathbb{K}$,
where the models of $M$ and $N$ have no boundary. If $f : M \to N$ and $g : N \to N'$ are $C^n$
submersions, then so is $g \circ f$.

Here $f$ is a $C^n$ submersion when there is one normed space $F$ over $\mathbb{K}$ such that at
every $x \in M$ there are charts $\varphi$ of $M$ around $x$ and $\psi$ of $N$ around $f(x)$ in
the $C^n$ maximal atlases, with $f$ mapping the domain of $\varphi$ into the domain of $\psi$, and
a continuous linear equivalence $e : E \to E'' \times F$ such that
$\hat\psi \circ f \circ \hat\varphi^{-1} = \mathrm{pr}_1 \circ e$ on the image of $\hat\varphi$,
where $\hat\varphi$ and $\hat\psi$ denote the charts followed by the models with corners. -/
theorem _root_.Manifold.IsSubmersion.comp
    [I.Boundaryless] [J.Boundaryless]
    {f : M → N} {g : N → N'}
    (hg : IsSubmersion J J' n g) (hf : IsSubmersion I J n f) :
    IsSubmersion I J' n (g ∘ f) :=
  (hg.isSubmersionOfComplement_complement.comp
    hf.isSubmersionOfComplement_complement).isSubmersion

/--
**Composition of submersions at a point.** Let $\mathbb{K}$ be a nontrivially normed field, let
$n \in \mathbb{N} \cup \{\infty, \omega\}$, and let $M$, $N$, $N'$ be $C^n$ manifolds without
boundary over $\mathbb{K}$ modelled on Banach spaces. If $f : M \to N$ is a $C^n$ submersion at
$x \in M$ and $g : N \to N'$ is a $C^n$ submersion at $f(x)$, then $g \circ f$ is a $C^n$
submersion at $x$. Here $f$ is a $C^n$ submersion at $x$ when there are charts of the $C^n$
maximal atlases around $x$ and $f(x)$, the first mapped by $f$ into the second, in which $f$ reads
$(u, v) \mapsto u$ after a continuous linear identification of the model space of $M$ with the
product of the model space of $N$ and some normed space.

Proves `Wanted` entry `submersionAt_comp`.

Proof: Replace the first submersion's target chart by the second submersion's source chart, then
compose the two projection normal forms and use the product of their complements.

Sources:
Mathlib `Mathlib/Geometry/Manifold/Submersion.lean` TODO (`IsSubmersionAt.comp`);
J. Lee, Introduction to Smooth Manifolds, 2nd ed., Ch. 4.
-/
theorem submersionAt_comp
    [CompleteSpace E] [CompleteSpace E''] [CompleteSpace E''']
    [I.Boundaryless] [J.Boundaryless] [J'.Boundaryless]
    [IsManifold I n M] [IsManifold J n N] [IsManifold J' n N']
    {f : M → N} {g : N → N'} {x : M}
    (hf : IsSubmersionAt I J n f x) (hg : IsSubmersionAt J J' n g (f x)) :
    IsSubmersionAt I J' n (g ∘ f) x := by
  exact hg.comp hf

/--
**Composition of submersions.** Let $\mathbb{K}$ be a nontrivially normed field, let
$n \in \mathbb{N} \cup \{\infty, \omega\}$, and let $M$, $N$, $N'$ be $C^n$ manifolds without
boundary over $\mathbb{K}$ modelled on Banach spaces. If $f : M \to N$ and $g : N \to N'$ are
$C^n$ submersions, then so is $g \circ f$. Here $f$ is a $C^n$ submersion when there is one normed
space $F$ such that at every $x \in M$ there are charts of the $C^n$ maximal atlases around $x$ and
$f(x)$, the first mapped by $f$ into the second, in which $f$ reads $(u, v) \mapsto u$ after a
continuous linear identification of the model space of $M$ with the product of the model space of
$N$ and $F$.

Proves `Wanted` entry `submersion_comp`.

Proof: Apply the complement-level pointwise composition theorem using the two fixed global
complements, then package their product as the complement of the composite.

Sources:
Mathlib `Mathlib/Geometry/Manifold/Submersion.lean` TODO (`IsSubmersion.comp`);
J. Lee, Introduction to Smooth Manifolds, 2nd ed., Ch. 4.
-/
theorem submersion_comp
    [CompleteSpace E] [CompleteSpace E''] [CompleteSpace E''']
    [I.Boundaryless] [J.Boundaryless] [J'.Boundaryless]
    [IsManifold I n M] [IsManifold J n N] [IsManifold J' n N']
    {f : M → N} {g : N → N'}
    (hf : IsSubmersion I J n f) (hg : IsSubmersion J J' n g) :
    IsSubmersion I J' n (g ∘ f) := by
  exact hg.comp hf

end MathlibExt.Geometry.Manifold.SubmersionCompWanted
