/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import MathlibExt.Geometry.Manifold.Riemannian.Conformal
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Coordinate expressions of smooth Riemannian metrics in charts

This file provides the coordinate expression of a smooth Riemannian metric on a
manifold in a chart. It defines no conformal factory; conformal scaling is reused
from the merged `Bundle.ContMDiffRiemannianMetric.conformalScale` in
`MathlibExt.Geometry.Manifold.Riemannian.Conformal`.

For a metric `g` and a chart `e`, `Manifold.metricInCoordinates g e` is the pullback
of `g` by the inverse extended chart `(e.extend I).symm`. Its matrix in a basis of the
model space is the coefficient matrix `g_ij = g (∂_i, ∂_j)` of the chart, as in
J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., GTM 176, 2018, Ch. 2.
It is the object whose derivatives up to order `k` define the `C^k` topology of
K. Burns and V. S. Matveev, *Open problems and questions about geodesics*,
Ergodic Theory Dynam. Systems 41 (2021) 641-684, §8.3 (arXiv:1308.5417v2 §8.4).
Values outside the chart target are irrelevant and are never used.

Main definitions:
* `Manifold.metricInCoordinates`: the Gram matrix field of `g` in the chart `e`.
* `Manifold.metricInCoordinates_apply`: pointwise formula for the above.
* `Manifold.metricInCoordinates_conformalScale`: scaling behaviour under the merged
  `Bundle.ContMDiffRiemannianMetric.conformalScale`.
* `Manifold.contDiffOn_metricInCoordinates`: smoothness on the chart target.
-/

@[expose] public section

open scoped ContDiff Manifold
open Bundle

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Coordinate expression of a Riemannian metric.** Let $g$ be a smooth Riemannian metric on
the tangent bundle of a smooth manifold $M$ modeled through a model with corners $I : H \to E$,
and let $e$ be an open partial homeomorphism from $M$ to $H$. Write $\psi$ for the inverse of the
extended chart $I \circ e$, $T$ for the target of $I \circ e$, and $D\psi(x)$ for the derivative
of $\psi$ at $x$ within $T$. The coordinate expression of $g$ in $e$ is the field of continuous
bilinear forms on $E$ that assigns to each $x \in E$ the pullback form
$(v, w) \mapsto g_{\psi(x)}(D\psi(x)\,v, D\psi(x)\,w)$. -/
noncomputable def metricInCoordinates
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (e : OpenPartialHomeomorph M H) : E → E →L[ℝ] E →L[ℝ] ℝ :=
  fun x =>
    (show E →L[ℝ] E →L[ℝ] ℝ from g.inner ((e.extend I).symm x)).bilinearComp
      (show E →L[ℝ] E from
        mfderivWithin 𝓘(ℝ, E) I (e.extend I).symm (e.extend I).target x)
      (show E →L[ℝ] E from
        mfderivWithin 𝓘(ℝ, E) I (e.extend I).symm (e.extend I).target x)

/-- **Pointwise formula for a metric in coordinates.** Let $g$ be a smooth Riemannian metric
on the tangent bundle of a smooth manifold $M$ modeled through a model with corners
$I : H \to E$, and let $e$ be an open partial homeomorphism from $M$ to $H$. Write $g^e$ for the
coordinate expression of $g$ in $e$, $\psi$ for the inverse of the extended chart $I \circ e$,
$T$ for the target of $I \circ e$, and $D\psi(x)$ for the derivative of $\psi$ at $x$ within
$T$. Then for all $x, v, w \in E$ we have
$g^e(x)(v, w) = g_{\psi(x)}(D\psi(x)\,v, D\psi(x)\,w)$. -/
@[simp]
theorem metricInCoordinates_apply
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (e : OpenPartialHomeomorph M H) (x v w : E) :
    metricInCoordinates g e x v w =
      g.inner ((e.extend I).symm x)
        (mfderivWithin 𝓘(ℝ, E) I (e.extend I).symm (e.extend I).target x v)
        (mfderivWithin 𝓘(ℝ, E) I (e.extend I).symm (e.extend I).target x w) := by
  simp only [metricInCoordinates]
  exact ContinuousLinearMap.bilinearComp_apply _ _ _ _ _

/-- **Conformal scaling of a metric in coordinates.** Let $g$ be a smooth Riemannian metric on
the tangent bundle of a smooth manifold $M$ modeled through a model with corners $I : H \to E$,
let $u : M \to \mathbb{R}$ be a smooth function with $u(p) > 0$ for every $p \in M$, and let $e$
be an open partial homeomorphism from $M$ to $H$. Write $g^e$ for the coordinate expression of
$g$ in $e$ and $\psi$ for the inverse of the extended chart $I \circ e$. Then for every $x \in E$
the coordinate expression of the conformally scaled metric $u g$ satisfies
$(u g)^e(x) = u(\psi(x))\, g^e(x)$. -/
theorem metricInCoordinates_conformalScale
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hpos : ∀ x, 0 < u x)
    (e : OpenPartialHomeomorph M H) (x : E) :
    metricInCoordinates (g.conformalScale u hu hpos) e x =
      u ((e.extend I).symm x) • metricInCoordinates g e x := by
  ext v w
  simp only [metricInCoordinates_apply,
    Bundle.ContMDiffRiemannianMetric.conformalScale_inner_apply, smul_apply,
    smul_eq_mul]

/-- **Smoothness of a metric in coordinates.** Let $E$ be a finite-dimensional real normed
space, let $M$ be a smooth manifold modeled through a model with corners $I : H \to E$, and let
$g$ be a smooth Riemannian metric on the tangent bundle of $M$. For every chart $e$ in the maximal
smooth atlas of $M$, the coordinate expression of $g$ in $e$, viewed as a map from $E$ to the
continuous bilinear forms on $E$, is $C^\infty$ on the target of the extended chart $I \circ e$. -/
theorem contDiffOn_metricInCoordinates [FiniteDimensional ℝ E]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M) :
    ContDiffOn ℝ ∞ (metricInCoordinates g e) (e.extend I).target := by
  have hψ : ContMDiffOn 𝓘(ℝ, E) I ∞ ⇑(e.extend I).symm (↑I '' e.target) :=
    contMDiffOn_extend_symm he
  have htarget : (e.extend I).target = ↑I '' e.target :=
    OpenPartialHomeomorph.extend_target' e
  have hψs : ContMDiffOn 𝓘(ℝ, E) I ∞ ⇑(e.extend I).symm (e.extend I).target := by
    rw [htarget]
    exact hψ
  have huniqDiff : UniqueDiffOn ℝ (e.extend I).target := by
    rw [OpenPartialHomeomorph.extend_target]
    exact ModelWithCorners.uniqueDiffOn_preimage I e.open_target
  have huniqMD : UniqueMDiff[(e.extend I).target] :=
    huniqDiff.uniqueMDiffOn
  have heq : (∞ : ℕ∞ω) + 1 = (∞ : ℕ∞ω) := by simp
  have hle : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := heq.le
  have htan : ContMDiffOn (𝓘(ℝ, E)).tangent I.tangent ∞
      (tangentMapWithin (𝓘(ℝ, E)) I ⇑(e.extend I).symm (e.extend I).target)
      (TotalSpace.proj ⁻¹' (e.extend I).target) :=
    ContMDiffOn.contMDiffOn_tangentMapWithin hψs hle huniqMD
  rw [contDiffOn_clm_apply]
  intro v
  rw [contDiffOn_clm_apply]
  intro w
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  -- The body ascription keeps the inferred codomain `ModelProd E E` (with
  -- `chartedSpaceSelf`), matching `hsymm` below; a plain `(x, v)` would
  -- elaborate with `Prod.mk` to `E × E` with `prodChartedSpace`.
  have hprod_v : ContMDiffOn (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun x : E => (show ModelProd E E from (x, v))) (e.extend I).target := by
    -- Rewrite the product model as a self model so that
    -- `contMDiffOn_iff_contDiffOn` applies.
    rw [← modelWithCornersSelf_prod]
    exact (contMDiffOn_iff_contDiffOn).mpr
      (ContDiffOn.prodMk contDiffOn_id contDiffOn_const)
  have hprod_w : ContMDiffOn (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun x : E => (show ModelProd E E from (x, w))) (e.extend I).target := by
    rw [← modelWithCornersSelf_prod]
    exact (contMDiffOn_iff_contDiffOn).mpr
      (ContDiffOn.prodMk contDiffOn_id contDiffOn_const)
  have hsymm : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ((𝓘(ℝ, E)).tangent) ∞
      (⇑(tangentBundleModelSpaceHomeomorph (𝓘(ℝ, E))).symm) Set.univ :=
    (contMDiff_tangentBundleModelSpaceHomeomorph_symm).contMDiffOn
  have hmaps_prod_v : Set.MapsTo (fun x : E => (show ModelProd E E from (x, v)))
      (e.extend I).target Set.univ :=
    Set.mapsTo_univ _ _
  have hmaps_prod_w : Set.MapsTo (fun x : E => (show ModelProd E E from (x, w)))
      (e.extend I).target Set.univ :=
    Set.mapsTo_univ _ _
  have hconst_v : ContMDiffOn (𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, v⟩ : TangentBundle (𝓘(ℝ, E)) E)) (e.extend I).target := by
    have hcomp : ContMDiffOn (𝓘(ℝ, E)) ((𝓘(ℝ, E)).tangent) ∞
        ((⇑(tangentBundleModelSpaceHomeomorph (𝓘(ℝ, E))).symm) ∘
          (fun x : E => (show ModelProd E E from (x, v)))) (e.extend I).target :=
      hsymm.comp hprod_v hmaps_prod_v
    exact hcomp
  have hconst_w : ContMDiffOn (𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, w⟩ : TangentBundle (𝓘(ℝ, E)) E)) (e.extend I).target := by
    have hcomp : ContMDiffOn (𝓘(ℝ, E)) ((𝓘(ℝ, E)).tangent) ∞
        ((⇑(tangentBundleModelSpaceHomeomorph (𝓘(ℝ, E))).symm) ∘
          (fun x : E => (show ModelProd E E from (x, w)))) (e.extend I).target :=
      hsymm.comp hprod_w hmaps_prod_w
    exact hcomp
  have hmaps_v : Set.MapsTo (fun x => (⟨x, v⟩ : TangentBundle (𝓘(ℝ, E)) E))
      (e.extend I).target (TotalSpace.proj ⁻¹' (e.extend I).target) := by
    intro x hx
    simpa using hx
  have hmaps_w : Set.MapsTo (fun x => (⟨x, w⟩ : TangentBundle (𝓘(ℝ, E)) E))
      (e.extend I).target (TotalSpace.proj ⁻¹' (e.extend I).target) := by
    intro x hx
    simpa using hx
  have hv_sec : ContMDiffOn (𝓘(ℝ, E)) (I.prod (𝓘(ℝ, E))) ∞
      (fun x => (⟨⇑(e.extend I).symm x,
        ((mfderivWithin (𝓘(ℝ, E)) I ⇑(e.extend I).symm (e.extend I).target x) v :
          TangentSpace I (⇑(e.extend I).symm x))⟩ :
        TotalSpace E (fun y : M ↦ TangentSpace I y))) (e.extend I).target :=
    htan.comp hconst_v hmaps_v
  have hw_sec : ContMDiffOn (𝓘(ℝ, E)) (I.prod (𝓘(ℝ, E))) ∞
      (fun x => (⟨⇑(e.extend I).symm x,
        ((mfderivWithin (𝓘(ℝ, E)) I ⇑(e.extend I).symm (e.extend I).target x) w :
          TangentSpace I (⇑(e.extend I).symm x))⟩ :
        TotalSpace E (fun y : M ↦ TangentSpace I y))) (e.extend I).target :=
    htan.comp hconst_w hmaps_w
  have heval : ContMDiffOn (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) ∞
      (fun x => inner ℝ
        ((mfderivWithin (𝓘(ℝ, E)) I ⇑(e.extend I).symm (e.extend I).target x) v :
          TangentSpace I (⇑(e.extend I).symm x))
        ((mfderivWithin (𝓘(ℝ, E)) I ⇑(e.extend I).symm (e.extend I).target x) w :
          TangentSpace I (⇑(e.extend I).symm x))) (e.extend I).target :=
    ContMDiffOn.inner_bundle hv_sec hw_sec
  have hevalDiff : ContDiffOn ℝ ∞
      (fun x => inner ℝ
        ((mfderivWithin (𝓘(ℝ, E)) I ⇑(e.extend I).symm (e.extend I).target x) v :
          TangentSpace I (⇑(e.extend I).symm x))
        ((mfderivWithin (𝓘(ℝ, E)) I ⇑(e.extend I).symm (e.extend I).target x) w :
          TangentSpace I (⇑(e.extend I).symm x))) (e.extend I).target :=
    (contMDiffOn_iff_contDiffOn).mp heval
  have heq : (fun x => inner ℝ
        ((mfderivWithin (𝓘(ℝ, E)) I ⇑(e.extend I).symm (e.extend I).target x) v :
          TangentSpace I (⇑(e.extend I).symm x))
        ((mfderivWithin (𝓘(ℝ, E)) I ⇑(e.extend I).symm (e.extend I).target x) w :
          TangentSpace I (⇑(e.extend I).symm x))) =
      (fun x => ((metricInCoordinates g e x) v) w) := by
    funext x
    rw [metricInCoordinates_apply]
    rfl
  rwa [heq] at hevalDiff

end Manifold
