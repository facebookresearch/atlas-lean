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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.MultiplierActions
public import MathlibExt.Analysis.CStarAlgebra.Seminorm

/-!
# Group invariance of Haar-core C-star seminorms

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Put L_g
f(s)=α_g(f(g⁻¹*s)) and R_g f(s)=δ(g)•f(s*g⁻¹), where δ(g)=Measure.modularCharacter g. Their
mixed products satisfy star(L_g f)*L_g h=star(f)*h and R_g f*star(R_g h)=f*star(h). Every
C-star seminorm p on the core therefore satisfies p(L_g f)=p(f)=p(R_g f), including p=0.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

/-- **Mixed Gram product preserved by left translation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f,h and g∈G, put L_g f(s)=α_g(f(g⁻¹*s)). Then star(L_g f)*L_g h=star(f)*h, where * is twisted
convolution.
-/
theorem star_groupLeft_mul_groupLeft (g : G) (f h : Carrier μ α) :
    star (groupLeft μ α g f) * groupLeft μ α g h = star f * h := by
  change convolution μ α (crossedStar μ α (groupLeft μ α g f)) (groupLeft μ α g h) =
    convolution μ α (crossedStar μ α f) h
  rw [crossedStar_groupLeft]
  rw [← convolution_groupLeft μ α g⁻¹ (crossedStar μ α f) (groupLeft μ α g h)]
  have hCancel : groupLeft μ α g⁻¹ (groupLeft μ α g h) = h := by
    have hm := congrArg (fun T : Carrier μ α →ₗ[ℂ] Carrier μ α => T h)
      (groupLeft_mul μ α g⁻¹ g).symm
    simpa only [LinearMap.comp_apply, inv_mul_cancel, groupLeft_one, LinearMap.id_apply] using hm
  rw [hCancel]

/-- **Mixed reversed Gram product preserved by right translation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For core coefficients
f,h and g∈G, put R_g f(s)=δ(g)•f(s*g⁻¹), where δ(g)=Measure.modularCharacter g. Then R_g
f*star(R_g h)=f*star(h), with twisted convolution.
-/
theorem groupRight_mul_star_groupRight (g : G) (f h : Carrier μ α) :
    groupRight μ α g f * star (groupRight μ α g h) = f * star h := by
  change convolution μ α (groupRight μ α g f) (crossedStar μ α (groupRight μ α g h)) =
    convolution μ α f (crossedStar μ α h)
  rw [crossedStar_groupRight]
  rw [← convolution_groupLeft μ α g f (groupLeft μ α g⁻¹ (crossedStar μ α h))]
  have hCancel : groupLeft μ α g (groupLeft μ α g⁻¹ (crossedStar μ α h)) = crossedStar μ α h := by
    have hm := congrArg (fun T : Carrier μ α →ₗ[ℂ] Carrier μ α => T (crossedStar μ α h))
      (groupLeft_mul μ α g g⁻¹).symm
    simpa only [LinearMap.comp_apply, mul_inv_cancel, groupLeft_one, LinearMap.id_apply] using hm
  rw [hCancel]

/-- **Left group invariance of a C-star seminorm.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For every C-star
seminorm p on Carrier μ α, g∈G and core coefficient f, p(groupLeft μ α g f)=p(f), where
groupLeft g f(s)=α_g(f(g⁻¹*s)).
-/
theorem cstarSeminorm_groupLeft (p : CStarSeminorm (Carrier μ α)) (g : G) (f : Carrier μ α) :
    p (groupLeft μ α g f) = p f := by
  apply (sq_eq_sq₀ (apply_nonneg p (groupLeft μ α g f)) (apply_nonneg p f)).mp
  calc
    p (groupLeft μ α g f) ^ 2 = p (star (groupLeft μ α g f) * groupLeft μ α g f) :=
      (p.map_star_mul_self (groupLeft μ α g f)).symm
    _ = p (star f * f) := congrArg p (star_groupLeft_mul_groupLeft μ α g f f)
    _ = p f ^ 2 := p.map_star_mul_self f

/-- **Right group invariance of a C-star seminorm.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For every C-star
seminorm p on Carrier μ α, g∈G and core coefficient f, p(groupRight μ α g f)=p(f), where
groupRight g f(s)=δ(g)•f(s*g⁻¹) and δ(g)=Measure.modularCharacter g.
-/
theorem cstarSeminorm_groupRight (p : CStarSeminorm (Carrier μ α)) (g : G) (f : Carrier μ α) :
    p (groupRight μ α g f) = p f := by
  have hReverse (x : Carrier μ α) : p (x * star x) = p x ^ 2 := by
    simpa only [star_star, CStarSeminorm.map_star] using p.map_star_mul_self (star x)
  apply (sq_eq_sq₀ (apply_nonneg p (groupRight μ α g f)) (apply_nonneg p f)).mp
  calc
    p (groupRight μ α g f) ^ 2 = p (groupRight μ α g f * star (groupRight μ α g f)) :=
      (hReverse (groupRight μ α g f)).symm
    _ = p (f * star f) := congrArg p (groupRight_mul_star_groupRight μ α g f f)
    _ = p f ^ 2 := hReverse f

end

end HaarTwistedCore
