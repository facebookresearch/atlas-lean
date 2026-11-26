/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CompletedMultiplierPair
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.L1Translation
public import MathlibExt.Analysis.CStarAlgebra.Multiplier.Strict

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Strict continuity of completed group multipliers

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. Assume p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous core coefficient k. The group multiplier u_p(g) extends the
left action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g is viewed as a complex scalar. For every x∈Xp, the left and
right completed translation orbits are norm-continuous in g. The strict topology on the
multiplier algebra is the topology of pointwise norm convergence of both components: m_i→m
means m_i.fst(x)→m.fst(x) and m_i.snd(x)→m.snd(x) for every x∈Xp. Thus g↦u_p(g) is strictly
continuous; together with the coefficient multiplier homomorphism it forms a strictly
continuous covariant pair.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped Topology MultiplierAlgebra

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α)) (hp : p ∈ admissibleCStarSeminorms μ α)

include hp

/-- **L¹ bound for a dense translation orbit difference.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. Assume p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous core coefficient k. For g∈G and core coefficient f, put L_g
f(s)=α_g(f(g⁻¹*s)). Then dist(groupLeftCompletion μ α p g (ιp(f)),ιp(f))≤∫ s, ‖L_g f(s)-f(s)‖
∂μ.
-/
theorem dist_groupLeftCompletion_source_le (g : G) (f : Carrier μ α) :
    dist (groupLeftCompletion μ α p g (p.toNonUnitalCompletion f)) (p.toNonUnitalCompletion f) ≤
      l1Gauge μ α (groupLeft μ α g f - f) := by
  rw [dist_eq_norm, groupLeftCompletion_apply, ← map_sub, CStarSeminorm.norm_toNonUnitalCompletion]
  exact hp _

/-- **Continuity at the identity on dense completed coefficients.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. Assume p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous core coefficient k. For every core coefficient f,
g↦groupLeftCompletion μ α p g (ιp(f)) is norm-continuous at g=1; its value there is ιp(f).
-/
theorem groupLeftCompletion_source_continuousAt_one (f : Carrier μ α) :
    ContinuousAt (fun g : G => groupLeftCompletion μ α p g (p.toNonUnitalCompletion f)) 1 := by
  change Tendsto _ (𝓝 1) (𝓝 (groupLeftCompletion μ α p 1 (p.toNonUnitalCompletion f)))
  rw [groupLeftCompletion_apply, groupLeft_one, LinearMap.id_apply]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(tendsto_l1Gauge_groupLeft_sub μ α f).eventually (gt_mem_nhds hε)] with g hg
  exact (dist_groupLeftCompletion_source_le μ α p hp g f).trans_lt hg

/-- **Continuity at the identity of every left completion orbit.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. Assume p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous core coefficient k. For x∈Xp, the orbit g↦groupLeftCompletion μ
α p g x is norm-continuous at the identity 1∈G.
-/
theorem groupLeftCompletion_continuousAt_one (x : p.NonUnitalCompletion) :
    ContinuousAt (fun g : G => groupLeftCompletion μ α p g x) 1 := by
  change Tendsto _ (𝓝 1) (𝓝 (groupLeftCompletion μ α p 1 x))
  rw [groupLeftCompletion_one, ContinuousLinearMap.id_apply]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨f, hApprox⟩ := p.denseRange_toNonUnitalCompletion.exists_dist_lt x hthird
  have hCore : Tendsto (fun g : G => groupLeftCompletion μ α p g (p.toNonUnitalCompletion f))
      (𝓝 1) (𝓝 (p.toNonUnitalCompletion f)) := by
    have h := groupLeftCompletion_source_continuousAt_one μ α p hp f
    change Tendsto _ (𝓝 1) (𝓝 (groupLeftCompletion μ α p 1 (p.toNonUnitalCompletion f))) at h
    rw [groupLeftCompletion_apply, groupLeft_one, LinearMap.id_apply] at h
    exact h
  filter_upwards [Metric.tendsto_nhds.mp hCore (ε / 3) hthird] with g hg
  have hDist : dist (groupLeftCompletion μ α p g x)
      (groupLeftCompletion μ α p g (p.toNonUnitalCompletion f)) =
        dist x (p.toNonUnitalCompletion f) := by
    simpa only [dist_eq_norm, map_sub] using
      norm_groupLeftCompletion_apply μ α p g (x - p.toNonUnitalCompletion f)
  calc
    dist (groupLeftCompletion μ α p g x) x ≤
        dist (groupLeftCompletion μ α p g x)
          (groupLeftCompletion μ α p g (p.toNonUnitalCompletion f)) +
        dist (groupLeftCompletion μ α p g (p.toNonUnitalCompletion f)) x := dist_triangle _ _ _
    _ ≤ dist x (p.toNonUnitalCompletion f) +
        (dist (groupLeftCompletion μ α p g (p.toNonUnitalCompletion f))
          (p.toNonUnitalCompletion f) + dist (p.toNonUnitalCompletion f) x) := by
      rw [hDist]
      exact add_le_add le_rfl (dist_triangle _ _ _)
    _ < ε / 3 + (ε / 3 + ε / 3) :=
      add_lt_add hApprox (add_lt_add hg (by simpa only [dist_comm] using hApprox))
    _ = ε := by ring

/-- **Norm continuity of completed left group orbits.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. Assume p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous core coefficient k. For every x∈Xp, g↦groupLeftCompletion μ α p
g x is norm-continuous on G. On dense classes this action is ιp(f)↦ιp(s↦α_g(f(g⁻¹*s))).
-/
theorem continuous_groupLeftCompletion (x : p.NonUnitalCompletion) :
    Continuous (fun g : G => groupLeftCompletion μ α p g x) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  have hAtOne : Tendsto (fun g : G => groupLeftCompletion μ α p g x) (𝓝 1) (𝓝 x) := by
    have h := groupLeftCompletion_continuousAt_one μ α p hp x
    change Tendsto _ (𝓝 1) (𝓝 (groupLeftCompletion μ α p 1 x)) at h
    rw [groupLeftCompletion_one, ContinuousLinearMap.id_apply] at h
    exact h
  have hShift : Tendsto (fun g : G => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    have h := (continuous_const : Continuous (fun _ : G => g₀⁻¹)).mul
      (continuous_id : Continuous (id : G → G))
    have hfun : ((fun _ : G => g₀⁻¹) * (id : G → G)) = fun g : G => g₀⁻¹ * g := by
      funext g
      rw [Pi.mul_apply]
      rfl
    rw [hfun] at h
    simpa only [inv_mul_cancel] using h.tendsto g₀
  have hOrbit := ((groupLeftCompletion μ α p g₀).continuous.tendsto x).comp (hAtOne.comp hShift)
  have hfun : (fun g : G => groupLeftCompletion μ α p g₀
      (groupLeftCompletion μ α p (g₀⁻¹ * g) x)) = fun g : G => groupLeftCompletion μ α p g x := by
    funext g
    have h := congrArg (fun T : p.NonUnitalCompletion →L[ℂ] p.NonUnitalCompletion => T x)
      (groupLeftCompletion_mul μ α p g₀ (g₀⁻¹ * g)).symm
    simpa only [ContinuousLinearMap.comp_apply, mul_inv_cancel_left] using h
  simp only [Function.comp_def] at hOrbit
  rw [hfun] at hOrbit
  exact hOrbit

/-- **Norm continuity of completed right group orbits.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. Assume p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous core coefficient k. For every x∈Xp, g↦groupRightCompletion μ α
p g x is norm-continuous on G. On dense classes it is ιp(f)↦ιp(s↦δ(g)•f(s*g⁻¹)), with
δ(g)=Measure.modularCharacter g.
-/
theorem continuous_groupRightCompletion (x : p.NonUnitalCompletion) :
    Continuous (fun g : G => groupRightCompletion μ α p g x) := by
  have h := ((continuous_groupLeftCompletion μ α p hp (star x)).comp continuous_inv).star
  have hfun : star (fun g : G => groupLeftCompletion μ α p g⁻¹ (star x)) =
      fun g : G => groupRightCompletion μ α p g x := by
    funext g
    simpa only [Pi.star_apply, inv_inv, star_star] using
      star_groupLeftCompletion μ α p g⁻¹ (star x)
  simp only [Function.comp_def] at h
  rw [hfun] at h
  exact h

/-- **Strict continuity of the group multiplier map.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. Assume p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous core coefficient k. The group multiplier u_p(g) extends the
left action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g is viewed as a complex scalar. The strict topology on the
multiplier algebra is the topology of pointwise norm convergence of both components: m_i→m
means m_i.fst(x)→m.fst(x) and m_i.snd(x)→m.snd(x) for every x∈Xp. The map g↦groupMultiplier μ
α p g is continuous from G to this strict topology.
-/
theorem strictContinuous_groupMultiplier :
    DoubleCentralizer.StrictContinuous (groupMultiplier μ α p) := by
  let _ : TopologicalSpace 𝓜(ℂ, p.NonUnitalCompletion) :=
    DoubleCentralizer.strictTopology p.NonUnitalCompletion
  change Continuous (groupMultiplier μ α p)
  rw [continuous_iff_continuousAt]
  intro g
  change DoubleCentralizer.StrictTendsto (groupMultiplier μ α p) (𝓝 g) (groupMultiplier μ α p g)
  apply (DoubleCentralizer.strictTendsto_iff _ _ _).mpr
  intro x
  exact ⟨(continuous_groupLeftCompletion μ α p hp x).tendsto g,
    (continuous_groupRightCompletion μ α p hp x).tendsto g⟩

/-- **Strict continuity of the unitary multiplier representation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. Assume p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous core coefficient k. The group multiplier u_p(g) extends the
left action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g is viewed as a complex scalar. The strict topology on the
multiplier algebra is the topology of pointwise norm convergence of both components: m_i→m
means m_i.fst(x)→m.fst(x) and m_i.snd(x)→m.snd(x) for every x∈Xp. The inclusion of
groupUnitaryMultiplierHom μ α p:G→unitary(𝓜(ℂ,Xp)) into 𝓜(ℂ,Xp) is strictly continuous.
-/
theorem strictContinuous_groupUnitaryMultiplierHom :
    DoubleCentralizer.StrictContinuous (fun g : G =>
      (groupUnitaryMultiplierHom μ α p g : 𝓜(ℂ, p.NonUnitalCompletion))) := by
  simpa only [groupUnitaryMultiplierHom_coe] using strictContinuous_groupMultiplier μ α p hp

/-- **Strictly continuous canonical multiplier pair.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. Assume p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous core coefficient k. For a∈A, the multiplier j_p(a) has left and
right components extending L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). The group multiplier
u_p(g) extends the left action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g
f(s)=δ(g)•f(s*g⁻¹), where δ(g)=Measure.modularCharacter g is viewed as a complex scalar. The
pair canonicalStrictMultiplierPair μ α p hp consists of j_p and u_p satisfying
u_p(g)*j_p(a)*star(u_p(g))=j_p(α_g(a)), with g↦u_p(g) continuous for the topology of pointwise
norm convergence of both multiplier components.
-/
def canonicalStrictMultiplierPair :
    { pair : (A →⋆ₙₐ[ℂ] 𝓜(ℂ, p.NonUnitalCompletion)) ×
        (G →* unitary 𝓜(ℂ, p.NonUnitalCompletion)) //
      (∀ g : G, ∀ a : A,
        (pair.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) * pair.1 a *
          star (pair.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) = pair.1 (α g a)) ∧
      DoubleCentralizer.StrictContinuous (fun g : G => (pair.2 g : 𝓜(ℂ, p.NonUnitalCompletion))) } :=
  ⟨(canonicalMultiplierPair μ α p).val,
    (canonicalMultiplierPair μ α p).property, strictContinuous_groupUnitaryMultiplierHom μ α p hp⟩

/-- **Underlying maps of the strict multiplier pair.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. Assume p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous core coefficient k. The coefficient and unitary group maps of
canonicalStrictMultiplierPair μ α p hp equal those of canonicalMultiplierPair μ α p:
coefficientMultiplierHom μ α p and groupUnitaryMultiplierHom μ α p.
-/
@[simp]
theorem canonicalStrictMultiplierPair_val :
    (canonicalStrictMultiplierPair μ α p hp).val = (canonicalMultiplierPair μ α p).val := rfl

/-- **Strict continuity carried by the canonical pair.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. Assume p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous core coefficient k. For the unitary group map u_p in
canonicalStrictMultiplierPair μ α p hp, g↦u_p(g).fst(x) and g↦u_p(g).snd(x) are
norm-continuous for every x∈Xp; this is strict continuity.
-/
theorem canonicalStrictMultiplierPair_strictContinuous :
    DoubleCentralizer.StrictContinuous (fun g : G =>
      ((canonicalStrictMultiplierPair μ α p hp).val.2 g : 𝓜(ℂ, p.NonUnitalCompletion))) :=
  (canonicalStrictMultiplierPair μ α p hp).property.2

/-- **Covariance of the strict multiplier pair.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. Assume p(k)≤q(k)=∫ s, ‖k(s)‖ ∂μ for every
compactly supported continuous core coefficient k. The maps j_p,u_p of
canonicalStrictMultiplierPair μ α p hp satisfy u_p(g)*j_p(a)*star(u_p(g))=j_p(α_g(a)) for all
g∈G and a∈A.
-/
theorem canonicalStrictMultiplierPair_covariance (g : G) (a : A) :
    ((canonicalStrictMultiplierPair μ α p hp).val.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) *
        (canonicalStrictMultiplierPair μ α p hp).val.1 a *
          star ((canonicalStrictMultiplierPair μ α p hp).val.2 g : 𝓜(ℂ, p.NonUnitalCompletion)) =
      (canonicalStrictMultiplierPair μ α p hp).val.1 (α g a) :=
  (canonicalStrictMultiplierPair μ α p hp).property.1 g a

end

end HaarTwistedCore
