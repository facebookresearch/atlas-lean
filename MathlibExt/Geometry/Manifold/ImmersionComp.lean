/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module


public import Mathlib.Geometry.Manifold.Immersion

/-!
# Composition of smooth immersions

This file proves that pointwise and global `C^n` immersions are closed under composition when the
intermediate and target models are boundaryless, for arbitrary differentiability order `n`. No
completeness hypothesis on the model spaces is needed.
-/

@[expose] public section

open scoped Topology ContDiff
open Manifold

noncomputable section

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} {E'' E''' : Type u}
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

private def immersionCompEquiv {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (e₁ : (E × F₁) ≃L[𝕜] E'') (e₂ : (E'' × F₂) ≃L[𝕜] E''') :
    (E × (F₁ × F₂)) ≃L[𝕜] E''' :=
  (ContinuousLinearEquiv.prodAssoc 𝕜 E F₁ F₂).symm |>.trans
    (e₁.prodCongr (ContinuousLinearEquiv.refl 𝕜 F₂)) |>.trans e₂

private lemma immersionCompEquiv_apply_zero {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (e₁ : (E × F₁) ≃L[𝕜] E'') (e₂ : (E'' × F₂) ≃L[𝕜] E''') (z : E) :
    immersionCompEquiv e₁ e₂ (z, 0) = e₂ (e₁ (z, 0), 0) := by
  rw [show (0 : F₁ × F₂) = (0, 0) by rfl]
  change e₂ ((e₁.prodCongr (ContinuousLinearEquiv.refl 𝕜 F₂))
    ((ContinuousLinearEquiv.prodAssoc 𝕜 E F₁ F₂).symm (z, (0, 0)))) = _
  rw [ContinuousLinearEquiv.prodAssoc_symm_apply]
  rfl

private def immersionCompCoordChange [J.Boundaryless]
    (e e' : OpenPartialHomeomorph N G) : OpenPartialHomeomorph E'' E'' :=
  J.toHomeomorph.symm.transOpenPartialHomeomorph <|
    (e.symm.trans e').transHomeomorph J.toHomeomorph

omit [ChartedSpace G N] in
private lemma immersionCompCoordChange_apply [J.Boundaryless]
    (e e' : OpenPartialHomeomorph N G) (z : E'') :
    immersionCompCoordChange (J := J) e e' z = J.extendCoordChange e e' z := by
  simp [immersionCompCoordChange, ModelWithCorners.extendCoordChange, Function.comp_def]

omit [ChartedSpace G N] in
private lemma immersionCompCoordChange_source [J.Boundaryless]
    (e e' : OpenPartialHomeomorph N G) :
    (immersionCompCoordChange (J := J) e e').source = (J.extendCoordChange e e').source := by
  ext z
  simp [immersionCompCoordChange, ModelWithCorners.toHomeomorph_symm_apply,
    J.range_eq_univ, Set.preimage_comp]

omit [ChartedSpace G N] in
private lemma immersionCompCoordChange_target [J.Boundaryless]
    (e e' : OpenPartialHomeomorph N G) :
    (immersionCompCoordChange (J := J) e e').target = (J.extendCoordChange e e').target := by
  ext z
  simp [immersionCompCoordChange, ModelWithCorners.toHomeomorph_symm_apply,
    J.range_eq_univ, Set.preimage_comp]

private lemma immersionCompCoordChange_contDiffOn [J.Boundaryless]
    (e e' : OpenPartialHomeomorph N G)
    (he : e ∈ IsManifold.maximalAtlas J n N)
    (he' : e' ∈ IsManifold.maximalAtlas J n N) :
    ContDiffOn 𝕜 n (immersionCompCoordChange (J := J) e e')
      (immersionCompCoordChange (J := J) e e').source := by
  rw [immersionCompCoordChange_source]
  exact (J.contDiffOn_extendCoordChange he he').congr fun z _ ↦
    immersionCompCoordChange_apply e e' z

omit [ChartedSpace G N] in
private lemma immersionCompCoordChange_symm_apply [J.Boundaryless]
    (e e' : OpenPartialHomeomorph N G) (z : E'') :
    (immersionCompCoordChange (J := J) e e').symm z =
      (J.extendCoordChange e e').symm z := by
  simp [immersionCompCoordChange, ModelWithCorners.extendCoordChange, Function.comp_def]

private lemma immersionCompCoordChange_symm_contDiffOn [J.Boundaryless]
    (e e' : OpenPartialHomeomorph N G)
    (he : e ∈ IsManifold.maximalAtlas J n N)
    (he' : e' ∈ IsManifold.maximalAtlas J n N) :
    ContDiffOn 𝕜 n (immersionCompCoordChange (J := J) e e').symm
      (immersionCompCoordChange (J := J) e e').target := by
  rw [immersionCompCoordChange_target]
  exact (J.contDiffOn_extendCoordChange_symm he he').congr fun z _ ↦
    immersionCompCoordChange_symm_apply e e' z

private def immersionCompTargetChange {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G) :
    OpenPartialHomeomorph E''' E''' :=
  e₂.toHomeomorph.symm.transOpenPartialHomeomorph <|
    ((immersionCompCoordChange (J := J) e e').symm.prod
      (OpenPartialHomeomorph.refl F)).transHomeomorph e₂.toHomeomorph

omit [ChartedSpace G N] in
private lemma immersionCompTargetChange_source {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G) :
    (immersionCompTargetChange (J := J) e₂ e e').source =
      e₂.symm ⁻¹' ((immersionCompCoordChange (J := J) e e').target ×ˢ Set.univ) := by
  simp [immersionCompTargetChange]

omit [ChartedSpace G N] in
private lemma immersionCompTargetChange_target {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G) :
    (immersionCompTargetChange (J := J) e₂ e e').target =
      e₂.symm ⁻¹' ((immersionCompCoordChange (J := J) e e').source ×ˢ Set.univ) := by
  simp [immersionCompTargetChange]

omit [ChartedSpace G N] in
private lemma immersionCompTargetChange_apply {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G) (z : E''') :
    immersionCompTargetChange (J := J) e₂ e e' z =
      e₂ ((immersionCompCoordChange (J := J) e e').symm (e₂.symm z).1, (e₂.symm z).2) := by
  simp [immersionCompTargetChange]

omit [ChartedSpace G N] in
private lemma immersionCompTargetChange_symm_apply {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G) (z : E''') :
    (immersionCompTargetChange (J := J) e₂ e e').symm z =
      e₂ (immersionCompCoordChange (J := J) e e' (e₂.symm z).1, (e₂.symm z).2) := by
  simp [immersionCompTargetChange]

private lemma immersionCompTargetChange_contDiffOn {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G)
    (he : e ∈ IsManifold.maximalAtlas J n N)
    (he' : e' ∈ IsManifold.maximalAtlas J n N) :
    ContDiffOn 𝕜 n (immersionCompTargetChange (J := J) e₂ e e')
      (immersionCompTargetChange (J := J) e₂ e e').source := by
  rw [immersionCompTargetChange_source]
  have hprod := (immersionCompCoordChange_symm_contDiffOn e e' he he').prodMap
    (by fun_prop : ContDiffOn 𝕜 n (id : F → F) Set.univ)
  have hin := hprod.comp (by fun_prop : ContDiffOn 𝕜 n e₂.symm
    (e₂.symm ⁻¹' ((immersionCompCoordChange (J := J) e e').target ×ˢ Set.univ)))
    (fun _ hz ↦ hz)
  have hout := (by fun_prop : ContDiff 𝕜 n e₂).comp_contDiffOn hin
  exact hout.congr fun z _ ↦ by
    simpa [Function.comp_def, Prod.map] using immersionCompTargetChange_apply e₂ e e' z

private lemma immersionCompTargetChange_symm_contDiffOn {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G)
    (he : e ∈ IsManifold.maximalAtlas J n N)
    (he' : e' ∈ IsManifold.maximalAtlas J n N) :
    ContDiffOn 𝕜 n (immersionCompTargetChange (J := J) e₂ e e').symm
      (immersionCompTargetChange (J := J) e₂ e e').target := by
  rw [immersionCompTargetChange_target]
  have hprod := (immersionCompCoordChange_contDiffOn e e' he he').prodMap
    (by fun_prop : ContDiffOn 𝕜 n (id : F → F) Set.univ)
  have hin := hprod.comp (by fun_prop : ContDiffOn 𝕜 n e₂.symm
    (e₂.symm ⁻¹' ((immersionCompCoordChange (J := J) e e').source ×ˢ Set.univ)))
    (fun _ hz ↦ hz)
  have hout := (by fun_prop : ContDiff 𝕜 n e₂).comp_contDiffOn hin
  exact hout.congr fun z _ ↦ by
    simpa [Function.comp_def, Prod.map] using immersionCompTargetChange_symm_apply e₂ e e' z

private def immersionCompModelTargetChange {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G) :
    OpenPartialHomeomorph G' G' :=
  J'.toHomeomorph.transOpenPartialHomeomorph <|
    (immersionCompTargetChange (J := J) e₂ e e').transHomeomorph J'.toHomeomorph.symm

private lemma immersionCompModelTargetChange_mem_contDiffGroupoid {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G)
    (he : e ∈ IsManifold.maximalAtlas J n N)
    (he' : e' ∈ IsManifold.maximalAtlas J n N) :
    immersionCompModelTargetChange (J := J) (J' := J') e₂ e e' ∈ contDiffGroupoid n J' := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · change ContDiffOn 𝕜 n _ _
    convert immersionCompTargetChange_contDiffOn e₂ e e' he he' using 1 <;>
      ext z <;> simp [immersionCompModelTargetChange, Function.comp_def,
        ModelWithCorners.toHomeomorph_apply, J'.range_eq_univ]
  · change ContDiffOn 𝕜 n _ _
    convert immersionCompTargetChange_symm_contDiffOn e₂ e e' he he' using 1 <;>
      ext z <;> simp [immersionCompModelTargetChange, Function.comp_def,
        ModelWithCorners.toHomeomorph_apply, J'.range_eq_univ]

private lemma immersionComp_trans_mem_maximalAtlas
    {e : OpenPartialHomeomorph N' G'} {p : OpenPartialHomeomorph G' G'}
    (he : e ∈ IsManifold.maximalAtlas J' n N') (hp : p ∈ contDiffGroupoid n J') :
    e.trans p ∈ IsManifold.maximalAtlas J' n N' := by
  rw [IsManifold.mem_maximalAtlas_iff] at he ⊢
  intro e' he'
  constructor
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid n J').trans ((contDiffGroupoid n J').symm hp) (he e' he').1
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid n J').trans (he e' he').2 hp

private def immersionCompCodChart {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G)
    (codChart : OpenPartialHomeomorph N' G') : OpenPartialHomeomorph N' G' :=
  codChart.trans (immersionCompModelTargetChange (J := J) (J' := J') e₂ e e')

private lemma immersionCompCodChart_mem_maximalAtlas {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G)
    (codChart : OpenPartialHomeomorph N' G')
    (he : e ∈ IsManifold.maximalAtlas J n N)
    (he' : e' ∈ IsManifold.maximalAtlas J n N)
    (hcod : codChart ∈ IsManifold.maximalAtlas J' n N') :
    immersionCompCodChart (J := J) (J' := J') e₂ e e' codChart ∈
      IsManifold.maximalAtlas J' n N' :=
  immersionComp_trans_mem_maximalAtlas hcod <|
    immersionCompModelTargetChange_mem_contDiffGroupoid e₂ e e' he he'

omit [ChartedSpace G N] [ChartedSpace G' N'] in
private lemma immersionCompCodChart_extend_apply {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G)
    (codChart : OpenPartialHomeomorph N' G') (z : N') :
    (immersionCompCodChart (J := J) (J' := J') e₂ e e' codChart).extend J' z =
      immersionCompTargetChange (J := J) e₂ e e' (codChart.extend J' z) := by
  simp [immersionCompCodChart, immersionCompModelTargetChange, Function.comp_def,
    ModelWithCorners.toHomeomorph_apply, J'.range_eq_univ]

omit [ChartedSpace G N] in
private lemma immersionCompCoordChange_mem_source [J.Boundaryless]
    (e e' : OpenPartialHomeomorph N G) (hsource : e.source ⊆ e'.source)
    {z : E''} (hz : z ∈ (e.extend J).target) :
    z ∈ (immersionCompCoordChange (J := J) e e').source := by
  rw [immersionCompCoordChange_source, ← OpenPartialHomeomorph.extend_image_source_inter]
  rw [← PartialEquiv.image_source_eq_target] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hye : y ∈ e.source := by simpa using hy
  exact ⟨y, ⟨hye, hsource hye⟩, rfl⟩

private lemma immersionComp_adapted_writtenInCharts {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
    {g : N → N'} {y : N} (hg : IsImmersionAtOfComplement F J J' n g y)
    (e : OpenPartialHomeomorph N G) (hsource : e.source ⊆ hg.domChart.source) :
    Set.EqOn
      ((immersionCompCodChart (J := J) (J' := J') hg.equiv e hg.domChart hg.codChart).extend J' ∘
        g ∘ (e.extend J).symm)
      (hg.equiv ∘ (·, 0)) (e.extend J).target := by
  intro z hz
  have hzθ := immersionCompCoordChange_mem_source e hg.domChart hsource hz
  have hp : (e.extend J).symm z ∈ hg.domChart.source := by
    apply hsource
    simpa only [OpenPartialHomeomorph.extend_source] using (e.extend J).map_target hz
  have hθ : immersionCompCoordChange (J := J) e hg.domChart z =
      hg.domChart.extend J ((e.extend J).symm z) := by
    rw [immersionCompCoordChange_apply]
    rfl
  have hθtarget : immersionCompCoordChange (J := J) e hg.domChart z ∈
      (hg.domChart.extend J).target := by
    rw [hθ]
    exact (hg.domChart.extend J).map_source (by simpa using hp)
  have hback : (hg.domChart.extend J).symm
      (immersionCompCoordChange (J := J) e hg.domChart z) = (e.extend J).symm z := by
    rw [hθ, (hg.domChart.extend J).left_inv (by simpa using hp)]
  have hnormal : hg.codChart.extend J'
      (g ((hg.domChart.extend J).symm
        (immersionCompCoordChange (J := J) e hg.domChart z))) =
      hg.equiv (immersionCompCoordChange (J := J) e hg.domChart z, 0) := by
    simpa [Function.comp_def] using hg.writtenInCharts hθtarget
  simp only [Function.comp_apply]
  rw [immersionCompCodChart_extend_apply, ← hback, hnormal, immersionCompTargetChange_apply]
  simp [hzθ]

omit [ChartedSpace G N] in
private lemma immersionCompModelTargetChange_mem_source_iff {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G) (z : G') :
    z ∈ (immersionCompModelTargetChange (J := J) (J' := J') e₂ e e').source ↔
      J' z ∈ (immersionCompTargetChange (J := J) e₂ e e').source := by
  simp [immersionCompModelTargetChange, ModelWithCorners.toHomeomorph_apply]

private lemma immersionComp_mem_codChart_source {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
    {g : N → N'} {y : N} (hg : IsImmersionAtOfComplement F J J' n g y)
    (e : OpenPartialHomeomorph N G) (hy : y ∈ e.source)
    (hsource : e.source ⊆ hg.domChart.source) :
    g y ∈ (immersionCompCodChart (J := J) (J' := J') hg.equiv e hg.domChart
      hg.codChart).source := by
  rw [immersionCompCodChart, OpenPartialHomeomorph.trans_source]
  refine ⟨hg.mem_codChart_source, ?_⟩
  change hg.codChart (g y) ∈
    (immersionCompModelTargetChange (J := J) (J' := J') hg.equiv e hg.domChart).source
  rw [immersionCompModelTargetChange_mem_source_iff]
  have hy' : y ∈ hg.domChart.source := hsource hy
  have hz : e.extend J y ∈ (e.extend J).target :=
    (e.extend J).map_source (by simpa using hy)
  have hzθ := immersionCompCoordChange_mem_source e hg.domChart hsource hz
  have heback : (e.extend J).symm (e.extend J y) = y :=
    (e.extend J).left_inv (by simpa using hy)
  have hθ : immersionCompCoordChange (J := J) e hg.domChart (e.extend J y) =
      hg.domChart.extend J y := by
    rw [immersionCompCoordChange_apply]
    change hg.domChart.extend J ((e.extend J).symm (e.extend J y)) = _
    rw [heback]
  have hθtarget := (immersionCompCoordChange (J := J) e hg.domChart).map_source hzθ
  have hnormal : hg.codChart.extend J' (g y) = hg.equiv (hg.domChart.extend J y, 0) := by
    have h := hg.writtenInCharts ((hg.domChart.extend J).map_source (by simpa using hy'))
    have hgback : (hg.domChart.extend J).symm (hg.domChart.extend J y) = y :=
      (hg.domChart.extend J).left_inv (by simpa using hy')
    simp only [Function.comp_apply] at h
    rwa [hgback] at h
  change J' (hg.codChart (g y)) ∈ _
  change hg.codChart.extend J' (g y) ∈ _
  rw [hnormal, immersionCompTargetChange_source]
  simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply, Set.mem_prod,
    Set.mem_univ, and_true]
  rwa [← hθ]

set_option maxHeartbeats 800000 in
-- The nested chart and partial-equivalence calculation needs extra elaboration budget.
/-- **Composition of immersions at a point with fixed complements.** Let $\mathbb{K}$ be a
nontrivially normed field, let $n \in \mathbb{N} \cup \{\infty, \omega\}$, and let $M$, $N$, $N'$
be charted spaces modelled through models with corners on normed spaces over $\mathbb{K}$, where
the models of $N$ and $N'$ are boundaryless. Let $F_1$ and $F_2$ be normed spaces over
$\mathbb{K}$. If $f : M \to N$ is a $C^n$ immersion at a point $x \in M$ with complement $F_1$
and $g : N \to N'$ is a $C^n$ immersion at $f(x)$ with complement $F_2$, then $g \circ f$ is a
$C^n$ immersion at $x$ with complement $F_1 \times F_2$.

Here a map is a $C^n$ immersion at a point with complement $F$ when there are charts of the
maximal $C^n$ atlases around the point and its image, the first mapped by the map into the
second, in which the map reads $u \mapsto \varphi(u, 0)$ for a continuous linear isomorphism
$\varphi$ from the product of the source model space with $F$ onto the target model space. -/
theorem _root_.Manifold.IsImmersionAtOfComplement.comp {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    [J.Boundaryless] [J'.Boundaryless]
    {f : M → N} {g : N → N'} {x : M}
    (hg : IsImmersionAtOfComplement F₂ J J' n g (f x))
    (hf : IsImmersionAtOfComplement F₁ I J n f x) :
    IsImmersionAtOfComplement (F₁ × F₂) I J' n (g ∘ f) x := by
  obtain ⟨s, hs, hsopen, hxs⟩ := mem_nhds_iff.mp <|
    hf.continuousAt (hg.domChart.open_source.mem_nhds hg.mem_domChart_source)
  let domChart := hf.domChart.restr s
  let midChart := hf.codChart.restr hg.domChart.source
  let codChart := immersionCompCodChart (J := J) (J' := J') hg.equiv midChart
    hg.domChart hg.codChart
  have hdom_source : domChart.source = hf.domChart.source ∩ s :=
    hf.domChart.restr_source' s hsopen
  have hmid_source_eq : midChart.source = hf.codChart.source ∩ hg.domChart.source :=
    hf.codChart.restr_source' hg.domChart.source hg.domChart.open_source
  have hmid_source : midChart.source ⊆ hg.domChart.source := by
    rw [hmid_source_eq]
    exact Set.inter_subset_right
  have hxdom : x ∈ domChart.source := by
    rw [hdom_source]
    exact ⟨hf.mem_domChart_source, hxs⟩
  have hxmid : f x ∈ midChart.source := by
    rw [hmid_source_eq]
    exact ⟨hf.mem_codChart_source, hg.mem_domChart_source⟩
  have hmap : domChart.source ⊆ f ⁻¹' midChart.source := by
    intro z hz
    rw [hdom_source] at hz
    rw [hmid_source_eq]
    exact ⟨hf.source_subset_preimage_source hz.1, hs hz.2⟩
  have hdom_mem : domChart ∈ IsManifold.maximalAtlas I n M := by
    exact restr_mem_maximalAtlas (contDiffGroupoid n I) hf.domChart_mem_maximalAtlas hsopen
  have hmid_mem : midChart ∈ IsManifold.maximalAtlas J n N := by
    exact restr_mem_maximalAtlas (contDiffGroupoid n J) hf.codChart_mem_maximalAtlas
      hg.domChart.open_source
  have hcod_mem : codChart ∈ IsManifold.maximalAtlas J' n N' :=
    immersionCompCodChart_mem_maximalAtlas hg.equiv midChart hg.domChart hg.codChart
      hmid_mem hg.domChart_mem_maximalAtlas hg.codChart_mem_maximalAtlas
  have hxcod : g (f x) ∈ codChart.source :=
    immersionComp_mem_codChart_source hg midChart hxmid hmid_source
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (hg.continuousAt.comp hf.continuousAt) (immersionCompEquiv hf.equiv hg.equiv)
    domChart codChart hxdom hxcod hdom_mem hcod_mem
  have hgWritten := immersionComp_adapted_writtenInCharts hg midChart hmid_source
  intro z hz
  let p := (domChart.extend I).symm z
  have hpdom : p ∈ domChart.source := by
    simpa [p] using (domChart.extend I).map_target hz
  have hp : p ∈ hf.domChart.source := by
    rw [hdom_source] at hpdom
    exact hpdom.1
  have hfz : hf.domChart.extend I p = z := by
    have h := (domChart.extend I).right_inv hz
    change domChart.extend I p = z at h
    rw [← h]
    rfl
  have hz' : z ∈ (hf.domChart.extend I).target := by
    rw [← hfz]
    exact (hf.domChart.extend I).map_source (by simpa using hp)
  have hfp : hf.codChart.extend J (f p) = hf.equiv (z, 0) := by
    have h := hf.writtenInCharts hz'
    have hback : (hf.domChart.extend I).symm z = p := by
      rw [← hfz, (hf.domChart.extend I).left_inv (by simpa using hp)]
    simpa only [Function.comp_apply, hback] using h
  have hpmid : f p ∈ midChart.source := hmap hpdom
  have hw : midChart.extend J (f p) = hf.equiv (z, 0) := by
    rw [show midChart.extend J (f p) = hf.codChart.extend J (f p) by rfl]
    exact hfp
  have hwt : midChart.extend J (f p) ∈ (midChart.extend J).target :=
    (midChart.extend J).map_source (by simpa using hpmid)
  have hgp := hgWritten hwt
  have hback : (midChart.extend J).symm (midChart.extend J (f p)) = f p :=
    (midChart.extend J).left_inv (by simpa using hpmid)
  simp only [Function.comp_apply, hback] at hgp
  change codChart.extend J' (g (f p)) = immersionCompEquiv hf.equiv hg.equiv (z, 0)
  rw [hgp, hw]
  exact (immersionCompEquiv_apply_zero hf.equiv hg.equiv z).symm

/-- **Composition of immersions at a point over boundaryless models.** Let $\mathbb{K}$ be a
nontrivially normed field, let $n \in \mathbb{N} \cup \{\infty, \omega\}$, and let $M$, $N$, $N'$
be charted spaces modelled through models with corners on normed spaces over $\mathbb{K}$, where
the models of $N$ and $N'$ are boundaryless. If $f : M \to N$ is a $C^n$ immersion at a point
$x \in M$ and $g : N \to N'$ is a $C^n$ immersion at $f(x)$, then $g \circ f$ is a $C^n$
immersion at $x$.

Here a map is a $C^n$ immersion at a point when, for some normed space $F$ over $\mathbb{K}$,
there are charts of the maximal $C^n$ atlases around the point and its image, the first mapped by
the map into the second, in which the map reads $u \mapsto \varphi(u, 0)$ for a continuous linear
isomorphism $\varphi$ from the product of the source model space with $F$ onto the target model
space. -/
theorem _root_.Manifold.IsImmersionAt.comp [J.Boundaryless] [J'.Boundaryless]
    {f : M → N} {g : N → N'} {x : M}
    (hg : IsImmersionAt J J' n g (f x)) (hf : IsImmersionAt I J n f x) :
    IsImmersionAt I J' n (g ∘ f) x :=
  (hg.isImmersionAtOfComplement_complement.comp
    hf.isImmersionAtOfComplement_complement).isImmersionAt

/-- **Composition of immersions with fixed complements.** Let $\mathbb{K}$ be a nontrivially normed
field, let $n \in \mathbb{N} \cup \{\infty, \omega\}$, and let $M$, $N$, $N'$ be charted spaces
modelled through models with corners on normed spaces over $\mathbb{K}$, where the models of $N$
and $N'$ are boundaryless. Let $F_1$ and $F_2$ be normed spaces over $\mathbb{K}$. If
$f : M \to N$ is a $C^n$ immersion with complement $F_1$ and $g : N \to N'$ is a $C^n$ immersion
with complement $F_2$, then $g \circ f$ is a $C^n$ immersion with complement $F_1 \times F_2$.

Here a map is a $C^n$ immersion with complement $F$ when for every point there are charts of the
maximal $C^n$ atlases around the point and its image, the first mapped by the map into the
second, in which the map reads $u \mapsto \varphi(u, 0)$ for a continuous linear isomorphism
$\varphi$ from the product of the source model space with $F$ onto the target model space. -/
theorem _root_.Manifold.IsImmersionOfComplement.comp {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    [J.Boundaryless] [J'.Boundaryless]
    {f : M → N} {g : N → N'}
    (hg : IsImmersionOfComplement F₂ J J' n g)
    (hf : IsImmersionOfComplement F₁ I J n f) :
    IsImmersionOfComplement (F₁ × F₂) I J' n (g ∘ f) :=
  fun x ↦ (hg (f x)).comp (hf x)

/-- **Composition of immersions over boundaryless models.** Let $\mathbb{K}$ be a nontrivially
normed field, let $n \in \mathbb{N} \cup \{\infty, \omega\}$, and let $M$, $N$, $N'$ be charted
spaces modelled through models with corners on normed spaces over $\mathbb{K}$, where the models
of $N$ and $N'$ are boundaryless. If $f : M \to N$ and $g : N \to N'$ are $C^n$ immersions, then
$g \circ f$ is a $C^n$ immersion.

Here a map is a $C^n$ immersion when there is a normed space $F$ over $\mathbb{K}$ such that for
every point there are charts of the maximal $C^n$ atlases around the point and its image, the
first mapped by the map into the second, in which the map reads $u \mapsto \varphi(u, 0)$ for a
continuous linear isomorphism $\varphi$ from the product of the source model space with $F$ onto
the target model space. -/
theorem _root_.Manifold.IsImmersion.comp [J.Boundaryless] [J'.Boundaryless]
    {f : M → N} {g : N → N'}
    (hg : IsImmersion J J' n g) (hf : IsImmersion I J n f) :
    IsImmersion I J' n (g ∘ f) :=
  (hg.isImmersionOfComplement_complement.comp
    hf.isImmersionOfComplement_complement).isImmersion

/--
**Composition of immersions at a point.** Let $\mathbb{K}$ be a nontrivially normed field, let
$n \in \mathbb{N} \cup \{\infty, \omega\}$, and let $M$, $N$, $N'$ be $C^n$ manifolds without
boundary modeled on Banach spaces over $\mathbb{K}$. If $f : M \to N$ is a $C^n$ immersion at a
point $x \in M$ and $g : N \to N'$ is a $C^n$ immersion at $f(x)$, then $g \circ f$ is a $C^n$
immersion at $x$.

Here a map is a $C^n$ immersion at a point when, in suitable charts around the point and its
image, it reads $u \mapsto \varphi(u, 0)$ for a continuous linear isomorphism
$\varphi : E \times F \to E'$, where $E$ and $E'$ are the model spaces of the source and target
and $F$ is some normed space over $\mathbb{K}$.

Proves `Wanted` entry `immersionAt_comp`.

Proof: Restrict the first immersion's codomain chart to the second immersion's domain chart, then
conjugate that chart transition through the second linear normal form. The normal forms compose
with the product of their complements.

Sources:
Mathlib `Mathlib/Geometry/Manifold/Immersion.lean` TODO (`IsImmersionAt.comp`);
J. Lee, Introduction to Smooth Manifolds, 2nd ed., Ch. 4.
-/
theorem immersionAt_comp
    [CompleteSpace E] [CompleteSpace E''] [CompleteSpace E''']
    [I.Boundaryless] [J.Boundaryless] [J'.Boundaryless]
    [IsManifold I n M] [IsManifold J n N] [IsManifold J' n N']
    {f : M → N} {g : N → N'} {x : M}
    (hf : IsImmersionAt I J n f x) (hg : IsImmersionAt J J' n g (f x)) :
    IsImmersionAt I J' n (g ∘ f) x := by
  exact hg.comp hf

/--
**Composition of immersions.** Let $\mathbb{K}$ be a nontrivially normed field, let
$n \in \mathbb{N} \cup \{\infty, \omega\}$, and let $M$, $N$, $N'$ be $C^n$ manifolds without
boundary modeled on Banach spaces over $\mathbb{K}$. If $f : M \to N$ and $g : N \to N'$ are
$C^n$ immersions, then $g \circ f$ is a $C^n$ immersion.

Here a map is a $C^n$ immersion when there is a normed space $F$ over $\mathbb{K}$ such that
around every point, in suitable charts around the point and its image, the map reads
$u \mapsto \varphi(u, 0)$ for some continuous linear isomorphism $\varphi : E \times F \to E'$,
where $E$ and $E'$ are the model spaces of the source and target.

Proves `Wanted` entry `immersion_comp`.

Proof: Apply the pointwise composition construction using the product of the two global
complements, then package the resulting fixed-complement immersion.

Sources:
Mathlib `Mathlib/Geometry/Manifold/Immersion.lean` TODO (`IsImmersion.comp`);
J. Lee, Introduction to Smooth Manifolds, 2nd ed., Ch. 4.
-/
theorem immersion_comp
    [CompleteSpace E] [CompleteSpace E''] [CompleteSpace E''']
    [I.Boundaryless] [J.Boundaryless] [J'.Boundaryless]
    [IsManifold I n M] [IsManifold J n N] [IsManifold J' n N']
    {f : M → N} {g : N → N'}
    (hf : IsImmersion I J n f) (hg : IsImmersion J J' n g) :
    IsImmersion I J' n (g ∘ f) := by
  exact hg.comp hf

end MathlibExt.Geometry.Manifold.ImmersionCompWanted
