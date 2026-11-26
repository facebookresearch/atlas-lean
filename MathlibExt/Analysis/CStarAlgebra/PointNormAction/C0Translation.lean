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

public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.ZeroAtInfty
public import MathlibExt.Analysis.CStarAlgebra.PointNormAction
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Tactic.Group

/-!
# Left translation on functions vanishing at infinity

For a topological group G, define λg on C₀(G,ℂ) by (λg f)(s) = f(g⁻¹s). Each λg is a complex
star-algebra automorphism, λgh = λg ∘ λh, and g ↦ λg f is continuous in the supremum norm for
every f. This gives the point-norm left-translation action without a discreteness or
separability assumption.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped ZeroAtInfty Uniformity

noncomputable section

open Filter Topology
open scoped CStarAlgebra

namespace PointNormCStarAction

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Left-translation automorphism of C₀(G).**

For a topological group G and g ∈ G, the automorphism λg of C₀(G,ℂ) is (λg f)(s) = f(g⁻¹s).
Its inverse is λg⁻¹.
-/
def c0LeftTranslationEquiv (g : G) : C₀(G, ℂ) ≃⋆ₐ[ℂ] C₀(G, ℂ) :=
  ZeroAtInftyContinuousMap.starAlgEquivPrecomp (A := ℂ) (Homeomorph.mulLeft g⁻¹)

/-- **Evaluation of a left translation.**

For g, s ∈ G and f ∈ C₀(G,ℂ), `c0LeftTranslationEquiv g f s = f (g⁻¹ * s)`.
-/
@[simp]
theorem c0LeftTranslationEquiv_apply (g : G) (f : C₀(G, ℂ)) (s : G) :
    c0LeftTranslationEquiv g f s = f (g⁻¹ * s) := rfl

/-- **Identity left translation.**

Translation by the group identity is the identity star-algebra automorphism of C₀(G,ℂ).
-/
@[simp]
theorem c0LeftTranslationEquiv_one : c0LeftTranslationEquiv (1 : G) = StarAlgEquiv.refl ℂ _ := by
  apply StarAlgEquiv.ext
  intro f
  apply ZeroAtInftyContinuousMap.ext
  intro s
  have hrefl : (StarAlgEquiv.refl ℂ C₀(G, ℂ)) f = f := rfl
  rw [hrefl, c0LeftTranslationEquiv_apply, inv_one, one_mul]

/-- **Composition of left translations.**

For g, h ∈ G, λgh = λg ∘ λh. The formula retains this order for a noncommutative group.
-/
theorem c0LeftTranslationEquiv_mul (g h : G) :
    c0LeftTranslationEquiv (g * h) = c0LeftTranslationEquiv g * c0LeftTranslationEquiv h := by
  apply StarAlgEquiv.ext
  intro f
  apply ZeroAtInftyContinuousMap.ext
  intro s
  change f ((g * h)⁻¹ * s) = f (h⁻¹ * (g⁻¹ * s))
  rw [mul_inv_rev, mul_assoc]

/-- **Supremum-norm continuity of translation orbits.**

For every f ∈ C₀(G,ℂ), the map g ↦ λg f is continuous in the supremum norm.
-/
theorem continuous_c0LeftTranslationEquiv_orbit (f : C₀(G, ℂ)) :
    Continuous (fun g : G => c0LeftTranslationEquiv g f) := by
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have hf : UniformContinuous (f : G → ℂ) := ZeroAtInftyContinuousMap.uniformContinuous f
  rw [continuous_iff_continuousAt]
  intro g0
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  have hu : {p : G × G | dist (f p.1) (f p.2) < epsilon / 2} ∈ 𝓤 G :=
    hf.eventually (Metric.dist_mem_uniformity hhalf)
  rw [_root_.uniformity_eq_comap_nhds_one' G] at hu
  rcases Filter.mem_comap.mp hu with ⟨V, hV, hsubset⟩
  have hnear : Tendsto (fun g : G => g⁻¹ * g0) (𝓝 g0) (𝓝 (1 : G)) := by
    have hcontinuous : Continuous (fun g : G => g⁻¹ * g0) :=
      continuous_inv.mul continuous_const
    have hlimit : Tendsto (fun g : G => g⁻¹ * g0) (𝓝 g0) (𝓝 (g0⁻¹ * g0)) :=
      hcontinuous.tendsto g0
    simpa only [inv_mul_cancel] using hlimit
  filter_upwards [hnear.eventually hV] with g hg
  have hbound : dist (c0LeftTranslationEquiv g f) (c0LeftTranslationEquiv g0 f) ≤ epsilon / 2 := by
    rw [← ZeroAtInftyContinuousMap.isometry_toBCF.dist_eq]
    apply (BoundedContinuousFunction.dist_le hhalf.le).2
    intro s
    have hproduct : (g⁻¹ * s) * (g0⁻¹ * s)⁻¹ = g⁻¹ * g0 := by group
    have hpair : (g0⁻¹ * s, g⁻¹ * s) ∈
        (fun p : G × G => p.2 * p.1⁻¹) ⁻¹' V := by
      change (g⁻¹ * s) * (g0⁻¹ * s)⁻¹ ∈ V
      rw [hproduct]
      exact hg
    have hdist := hsubset hpair
    simpa only [c0LeftTranslationEquiv_apply, dist_comm] using hdist.le
  exact hbound.trans_lt (half_lt_self hepsilon)

/-- **Point-norm left-translation action.**

The automorphisms (λg f)(s) = f(g⁻¹s) form a point-norm continuous action of the topological
group G on C₀(G,ℂ).
-/
def c0LeftTranslationAction : PointNormCStarAction G C₀(G, ℂ) where
  toMonoidHom :=
    { toFun := c0LeftTranslationEquiv
      map_one' := c0LeftTranslationEquiv_one
      map_mul' := c0LeftTranslationEquiv_mul }
  continuous_orbit := continuous_c0LeftTranslationEquiv_orbit

/-- **Evaluation of the translation action.**

For g, s ∈ G and f ∈ C₀(G,ℂ), `c0LeftTranslationAction g f s = f (g⁻¹ * s)`.
-/
@[simp]
theorem c0LeftTranslationAction_apply (g : G) (f : C₀(G, ℂ)) (s : G) :
    c0LeftTranslationAction g f s = f (g⁻¹ * s) := rfl

end PointNormCStarAction
