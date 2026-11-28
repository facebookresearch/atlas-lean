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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.Basic
public import MathlibExt.MeasureTheory.Group.ModularCharacterContinuity

/-!
# Modular involution of compact coefficients

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. Writing δ(s)=Measure.modularCharacter s, define
f⁎(s)=((δ(s):ℝ):ℂ)•α_s(star(f(s⁻¹))). For f∈C_c(G,A), this is again compactly supported and
continuous, with tsupport(f⁎)⊆tsupport(f)⁻¹. It is additive, conjugate-linear and involutive:
(f+h)⁎=f⁎+h⁎, (c•f)⁎=conj(c)•f⁎ and (f⁎)⁎=f.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set MeasureTheory
open scoped CompactlySupported NNReal Pointwise CStarAlgebra

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- **Modular adjoint of a compact coefficient.**

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. Writing δ(s)=Measure.modularCharacter s, define
f⁎(s)=((δ(s):ℝ):ℂ)•α_s(star(f(s⁻¹))). The compactly supported continuous function
crossedStarCc α f is f⁎ for f∈C_c(G,A).
-/
def crossedStarCc (α : PointNormCStarAction G A) (f : C_c(G, A)) : C_c(G, A) where
  toFun s := ((Measure.modularCharacter s : ℝ) : ℂ) • α s (star (f s⁻¹))
  continuous_toFun := by
    have hδ : Continuous (fun s : G => ((Measure.modularCharacter s : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        (continuous_subtype_val.comp Measure.continuous_modularCharacter)
    exact hδ.smul (α.continuous_apply continuous_id ((map_continuous f).comp continuous_inv).star)
  hasCompactSupport' := by
    refine HasCompactSupport.intro f.hasCompactSupport.inv ?_
    intro s hs
    have hzero : f s⁻¹ = 0 := by
      by_contra hne
      apply hs
      change s⁻¹ ∈ tsupport (f : G → A)
      exact subset_closure hne
    simp only [hzero, star_zero, PointNormCStarAction.apply_zero, smul_zero]

omit [MeasurableSpace G] in
/-- **Evaluation of the modular adjoint.**

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. For f∈C_c(G,A) and s∈G, crossedStarCc α f
s=((Measure.modularCharacter s:ℝ):ℂ)•α_s(star(f(s⁻¹))).
-/
@[simp]
theorem crossedStarCc_apply (α : PointNormCStarAction G A) (f : C_c(G, A)) (s : G) :
    crossedStarCc α f s = ((Measure.modularCharacter s : ℝ) : ℂ) • α s (star (f s⁻¹)) :=
  rfl

omit [MeasurableSpace G] in
/-- **Support of the modular adjoint.**

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. Writing δ(s)=Measure.modularCharacter s, define
f⁎(s)=((δ(s):ℝ):ℂ)•α_s(star(f(s⁻¹))). For f∈C_c(G,A), tsupport(f⁎)⊆tsupport(f)⁻¹, where
tsupport is the closure of the nonzero set.
-/
theorem tsupport_crossedStarCc_subset (α : PointNormCStarAction G A) (f : C_c(G, A)) :
    tsupport (crossedStarCc α f : G → A) ⊆ (tsupport (f : G → A))⁻¹ := by
  refine closure_minimal ?_ (isClosed_tsupport (f : G → A)).inv
  intro s hs
  have hne : f s⁻¹ ≠ 0 := by
    intro hzero
    apply hs
    simp only [crossedStarCc_apply, hzero, star_zero, PointNormCStarAction.apply_zero, smul_zero]
  change s⁻¹ ∈ tsupport (f : G → A)
  exact subset_closure hne

variable (μ : Measure G) (α : PointNormCStarAction G A)

/-- **Modular involution on core coefficients.**

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. Let μ be a measure on G with a measurable structure, and write
Carrier μ α for the compactly supported continuous coefficient core. Writing
δ(s)=Measure.modularCharacter s, define f⁎(s)=((δ(s):ℝ):ℂ)•α_s(star(f(s⁻¹))). The map
crossedStar μ α:Carrier μ α→Carrier μ α sends each coefficient f to f⁎.
-/
def crossedStar (f : Carrier μ α) : Carrier μ α :=
  fromCc μ α (crossedStarCc α (toCc μ α f))

/-- **Value of the core modular involution.**

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. Let μ be a measure on G with a measurable structure, and write
Carrier μ α for the compactly supported continuous coefficient core. For f∈Carrier μ α and
s∈G, crossedStar μ α f s=((Measure.modularCharacter s:ℝ):ℂ)•α_s(star(f(s⁻¹))).
-/
@[simp]
theorem crossedStar_apply (f : Carrier μ α) (s : G) :
    crossedStar μ α f s = ((Measure.modularCharacter s : ℝ) : ℂ) • α s (star (f s⁻¹)) :=
  rfl

/-- **Additivity of the modular involution.**

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. Let μ be a measure on G with a measurable structure, and write
Carrier μ α for the compactly supported continuous coefficient core. Writing
δ(s)=Measure.modularCharacter s, define f⁎(s)=((δ(s):ℝ):ℂ)•α_s(star(f(s⁻¹))). For f,h∈Carrier
μ α, (f+h)⁎=f⁎+h⁎.
-/
theorem crossedStar_add (f g : Carrier μ α) :
    crossedStar μ α (f + g) = crossedStar μ α f + crossedStar μ α g := by
  apply (equivCc μ α).injective
  change toCc μ α (crossedStar μ α (f + g)) =
    toCc μ α (crossedStar μ α f + crossedStar μ α g)
  rw [toCc_add]
  apply CompactlySupportedContinuousMap.ext
  intro s
  simp only [crossedStar, toCc_fromCc, crossedStarCc_apply, toCc_add,
    CompactlySupportedContinuousMap.add_apply, star_add, PointNormCStarAction.apply_add, smul_add]

/-- **Conjugate-linearity of the modular involution.**

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. Let μ be a measure on G with a measurable structure, and write
Carrier μ α for the compactly supported continuous coefficient core. Writing
δ(s)=Measure.modularCharacter s, define f⁎(s)=((δ(s):ℝ):ℂ)•α_s(star(f(s⁻¹))). For c∈ℂ and
f∈Carrier μ α, (c•f)⁎=star(c)•f⁎=conj(c)•f⁎.
-/
theorem crossedStar_smul (c : ℂ) (f : Carrier μ α) :
    crossedStar μ α (c • f) = star c • crossedStar μ α f := by
  apply (equivCc μ α).injective
  change toCc μ α (crossedStar μ α (c • f)) = toCc μ α (star c • crossedStar μ α f)
  rw [toCc_smul]
  apply CompactlySupportedContinuousMap.ext
  intro s
  simp only [crossedStar, toCc_fromCc, crossedStarCc_apply, toCc_smul,
    CompactlySupportedContinuousMap.smul_apply, star_smul, PointNormCStarAction.apply_smul]
  exact smul_comm _ _ _

/-- **The modular adjoint is involutive.**

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. Let μ be a measure on G with a measurable structure, and write
Carrier μ α for the compactly supported continuous coefficient core. Writing
δ(s)=Measure.modularCharacter s, define f⁎(s)=((δ(s):ℝ):ℂ)•α_s(star(f(s⁻¹))). Every f∈Carrier
μ α satisfies (f⁎)⁎=f.
-/
theorem crossedStar_crossedStar (f : Carrier μ α) :
    crossedStar μ α (crossedStar μ α f) = f := by
  apply (equivCc μ α).injective
  change toCc μ α (crossedStar μ α (crossedStar μ α f)) = toCc μ α f
  apply CompactlySupportedContinuousMap.ext
  intro s
  have hδ : ((Measure.modularCharacter s : ℝ) : ℂ) *
      ((Measure.modularCharacter s⁻¹ : ℝ) : ℂ) = 1 := by
    have h : Measure.modularCharacter s * Measure.modularCharacter s⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hreal : (Measure.modularCharacter s : ℝ) *
        (Measure.modularCharacter s⁻¹ : ℝ) = 1 := by exact_mod_cast h
    exact_mod_cast hreal
  have hstarδ : star ((Measure.modularCharacter s⁻¹ : ℝ) : ℂ) =
      ((Measure.modularCharacter s⁻¹ : ℝ) : ℂ) := by simp
  simp only [crossedStar, toCc_fromCc, crossedStarCc_apply, inv_inv]
  change ((Measure.modularCharacter s : ℝ) : ℂ) •
    α s (star (((Measure.modularCharacter s⁻¹ : ℝ) : ℂ) • α s⁻¹ (star (f s)))) = f s
  rw [star_smul, hstarδ, ← PointNormCStarAction.apply_star, star_star,
    PointNormCStarAction.apply_smul, PointNormCStarAction.apply_apply_inv, ← mul_smul, hδ, one_smul]

/-- **Star operation on the compact coefficient core.**

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. Let μ be a measure on G with a measurable structure, and write
Carrier μ α for the compactly supported continuous coefficient core. Writing
δ(s)=Measure.modularCharacter s, define f⁎(s)=((δ(s):ℝ):ℂ)•α_s(star(f(s⁻¹))). This modular
adjoint is the star operation of Carrier μ α.
-/
instance instStarCarrier : Star (Carrier μ α) :=
  ⟨crossedStar μ α⟩

/-- **Involutive star on core coefficients.**

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. Let μ be a measure on G with a measurable structure, and write
Carrier μ α for the compactly supported continuous coefficient core. Writing
δ(s)=Measure.modularCharacter s, define f⁎(s)=((δ(s):ℝ):ℂ)•α_s(star(f(s⁻¹))). The star
operation on Carrier μ α satisfies star(star(f))=f for every coefficient f.
-/
instance instInvolutiveStarCarrier : InvolutiveStar (Carrier μ α) where
  star_involutive := crossedStar_crossedStar μ α

/-- **Additive star structure on core coefficients.**

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. Let μ be a measure on G with a measurable structure, and write
Carrier μ α for the compactly supported continuous coefficient core. Writing
δ(s)=Measure.modularCharacter s, define f⁎(s)=((δ(s):ℝ):ℂ)•α_s(star(f(s⁻¹))). The pointwise
additive group Carrier μ α has star(f+h)=star(f)+star(h).
-/
instance instStarAddMonoidCarrier : StarAddMonoid (Carrier μ α) where
  star_add := crossedStar_add μ α

/-- **Complex star module of core coefficients.**

Let G be a locally compact topological group, A a nonunital complex C-star algebra and α a
point-norm action of G on A. Let μ be a measure on G with a measurable structure, and write
Carrier μ α for the compactly supported continuous coefficient core. Writing
δ(s)=Measure.modularCharacter s, define f⁎(s)=((δ(s):ℝ):ℂ)•α_s(star(f(s⁻¹))). Complex scaling
and the modular adjoint satisfy star(c•f)=star(c)•star(f), making Carrier μ α a complex star
module.
-/
instance instStarModuleCarrier : StarModule ℂ (Carrier μ α) where
  star_smul := crossedStar_smul μ α

end

end HaarTwistedCore
