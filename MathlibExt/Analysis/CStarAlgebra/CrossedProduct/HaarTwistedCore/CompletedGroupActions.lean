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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.SeminormGroupActions
public import MathlibExt.Analysis.CStarAlgebra.SeminormNonUnitalCompletion
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Group translations on a C-star seminorm completion

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let L_g,R_g:Xp→L[ℂ]Xp extend the coefficient translations
f(s)↦α_g(f(g⁻¹*s)) and f(s)↦δ(g)•f(s*g⁻¹), respectively, where δ(g)=Measure.modularCharacter g
is embedded in ℂ. Both actions are isometries, satisfy L_(gh)=L_g∘L_h and R_(gh)=R_h∘R_g, and
form a compatible centralizer pair: (R_g x)*y=x*(L_g y). These laws apply to the zero
seminorm.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] [μ.Regular]
  (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α))

/-- **Completed left group translation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let L_g,R_g:Xp→L[ℂ]Xp extend the coefficient translations
f(s)↦α_g(f(g⁻¹*s)) and f(s)↦δ(g)•f(s*g⁻¹), respectively, where δ(g)=Measure.modularCharacter g
is embedded in ℂ. The map groupLeftCompletion μ α p g is L_g, determined by
L_g(ιp(f))=ιp(s↦α_g(f(g⁻¹*s))).
-/
def groupLeftCompletion (g : G) : p.NonUnitalCompletion →L[ℂ] p.NonUnitalCompletion :=
  ((LinearMap.ofClass p.toNonUnitalCompletion).comp (groupLeft μ α g)).extendOfNorm
    (LinearMap.ofClass p.toNonUnitalCompletion)

/-- **Completed modular right group translation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let L_g,R_g:Xp→L[ℂ]Xp extend the coefficient translations
f(s)↦α_g(f(g⁻¹*s)) and f(s)↦δ(g)•f(s*g⁻¹), respectively, where δ(g)=Measure.modularCharacter g
is embedded in ℂ. The map groupRightCompletion μ α p g is R_g, determined by
R_g(ιp(f))=ιp(s↦δ(g)•f(s*g⁻¹)).
-/
def groupRightCompletion (g : G) : p.NonUnitalCompletion →L[ℂ] p.NonUnitalCompletion :=
  ((LinearMap.ofClass p.toNonUnitalCompletion).comp (groupRight μ α g)).extendOfNorm
    (LinearMap.ofClass p.toNonUnitalCompletion)

/-- **Left group translation on a dense coefficient class.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. For g∈G and f∈Carrier μ α, groupLeftCompletion μ α p g
(ιp(f))=ιp(s↦α_g(f(g⁻¹*s))).
-/
theorem groupLeftCompletion_apply (g : G) (f : Carrier μ α) :
    groupLeftCompletion μ α p g (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (groupLeft μ α g f) := by
  apply LinearMap.extendOfNorm_eq (p.denseRange_toNonUnitalCompletion)
  refine ⟨1, fun h => ?_⟩
  change ‖p.toNonUnitalCompletion (groupLeft μ α g h)‖ ≤
    1 * ‖p.toNonUnitalCompletion h‖
  simp only [CStarSeminorm.norm_toNonUnitalCompletion, cstarSeminorm_groupLeft, one_mul, le_rfl]

/-- **Right group translation on a dense coefficient class.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. For g∈G and f∈Carrier μ α, groupRightCompletion μ α p g
(ιp(f))=ιp(s↦δ(g)•f(s*g⁻¹)), where δ(g)=Measure.modularCharacter g.
-/
theorem groupRightCompletion_apply (g : G) (f : Carrier μ α) :
    groupRightCompletion μ α p g (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (groupRight μ α g f) := by
  apply LinearMap.extendOfNorm_eq (p.denseRange_toNonUnitalCompletion)
  refine ⟨1, fun h => ?_⟩
  change ‖p.toNonUnitalCompletion (groupRight μ α g h)‖ ≤
    1 * ‖p.toNonUnitalCompletion h‖
  simp only [CStarSeminorm.norm_toNonUnitalCompletion, cstarSeminorm_groupRight, one_mul, le_rfl]

/-- **Isometry of the completed left translation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let L_g,R_g:Xp→L[ℂ]Xp extend the coefficient translations
f(s)↦α_g(f(g⁻¹*s)) and f(s)↦δ(g)•f(s*g⁻¹), respectively, where δ(g)=Measure.modularCharacter g
is embedded in ℂ. For g∈G and x∈Xp, ‖L_g x‖=‖x‖.
-/
theorem norm_groupLeftCompletion_apply (g : G) (x : p.NonUnitalCompletion) :
    ‖groupLeftCompletion μ α p g x‖ = ‖x‖ := by
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupLeftCompletion μ α p g).continuous.norm continuous_norm ?_) x
  funext f
  simp only [Function.comp_apply, groupLeftCompletion_apply,
    CStarSeminorm.norm_toNonUnitalCompletion, cstarSeminorm_groupLeft]

/-- **Isometry of the completed right translation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let L_g,R_g:Xp→L[ℂ]Xp extend the coefficient translations
f(s)↦α_g(f(g⁻¹*s)) and f(s)↦δ(g)•f(s*g⁻¹), respectively, where δ(g)=Measure.modularCharacter g
is embedded in ℂ. For g∈G and x∈Xp, ‖R_g x‖=‖x‖.
-/
theorem norm_groupRightCompletion_apply (g : G) (x : p.NonUnitalCompletion) :
    ‖groupRightCompletion μ α p g x‖ = ‖x‖ := by
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupRightCompletion μ α p g).continuous.norm continuous_norm ?_) x
  funext f
  simp only [Function.comp_apply, groupRightCompletion_apply,
    CStarSeminorm.norm_toNonUnitalCompletion, cstarSeminorm_groupRight]

/-- **Identity in the completed left group action.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let L_g,R_g:Xp→L[ℂ]Xp extend the coefficient translations
f(s)↦α_g(f(g⁻¹*s)) and f(s)↦δ(g)•f(s*g⁻¹), respectively, where δ(g)=Measure.modularCharacter g
is embedded in ℂ. The group identity acts as L_1=id_Xp.
-/
@[simp]
theorem groupLeftCompletion_one : groupLeftCompletion μ α p (1 : G) = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupLeftCompletion μ α p 1).continuous continuous_id ?_) x
  funext f
  simp only [Function.comp_apply, groupLeftCompletion_apply, groupLeft_one, LinearMap.id_apply, id_eq]

/-- **Identity in the completed right group action.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let L_g,R_g:Xp→L[ℂ]Xp extend the coefficient translations
f(s)↦α_g(f(g⁻¹*s)) and f(s)↦δ(g)•f(s*g⁻¹), respectively, where δ(g)=Measure.modularCharacter g
is embedded in ℂ. The group identity acts as R_1=id_Xp.
-/
@[simp]
theorem groupRightCompletion_one : groupRightCompletion μ α p (1 : G) = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupRightCompletion μ α p 1).continuous continuous_id ?_) x
  funext f
  simp only [Function.comp_apply, groupRightCompletion_apply, groupRight_one, LinearMap.id_apply, id_eq]

/-- **Composition of completed left translations.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let L_g,R_g:Xp→L[ℂ]Xp extend the coefficient translations
f(s)↦α_g(f(g⁻¹*s)) and f(s)↦δ(g)•f(s*g⁻¹), respectively, where δ(g)=Measure.modularCharacter g
is embedded in ℂ. For g,h∈G, L_(g*h)=L_g∘L_h.
-/
theorem groupLeftCompletion_mul (g h : G) :
    groupLeftCompletion μ α p (g * h) =
      (groupLeftCompletion μ α p g).comp (groupLeftCompletion μ α p h) := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupLeftCompletion μ α p (g * h)).continuous
    ((groupLeftCompletion μ α p g).continuous.comp
      (groupLeftCompletion μ α p h).continuous) ?_) x
  funext f
  simp only [Function.comp_apply,
    groupLeftCompletion_apply, groupLeft_mul, LinearMap.comp_apply]

/-- **Reversed composition of completed right translations.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let L_g,R_g:Xp→L[ℂ]Xp extend the coefficient translations
f(s)↦α_g(f(g⁻¹*s)) and f(s)↦δ(g)•f(s*g⁻¹), respectively, where δ(g)=Measure.modularCharacter g
is embedded in ℂ. For g,h∈G, R_(g*h)=R_h∘R_g.
-/
theorem groupRightCompletion_mul (g h : G) :
    groupRightCompletion μ α p (g * h) =
      (groupRightCompletion μ α p h).comp (groupRightCompletion μ α p g) := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupRightCompletion μ α p (g * h)).continuous
    ((groupRightCompletion μ α p h).continuous.comp
      (groupRightCompletion μ α p g).continuous) ?_) x
  funext f
  simp only [Function.comp_apply,
    groupRightCompletion_apply, groupRight_mul, LinearMap.comp_apply]

/-- **Star exchanges left translation with inverse right translation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let L_g,R_g:Xp→L[ℂ]Xp extend the coefficient translations
f(s)↦α_g(f(g⁻¹*s)) and f(s)↦δ(g)•f(s*g⁻¹), respectively, where δ(g)=Measure.modularCharacter g
is embedded in ℂ. For g∈G and x∈Xp, star(L_g x)=R_(g⁻¹)(star(x)).
-/
theorem star_groupLeftCompletion (g : G) (x : p.NonUnitalCompletion) :
    star (groupLeftCompletion μ α p g x) = groupRightCompletion μ α p g⁻¹ (star x) := by
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupLeftCompletion μ α p g).continuous.star
    ((groupRightCompletion μ α p g⁻¹).continuous.comp continuous_star) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.star_apply,
    groupLeftCompletion_apply, ← map_star, groupRightCompletion_apply]
  exact congrArg p.toNonUnitalCompletion (crossedStar_groupLeft μ α g f)

/-- **Star exchanges right translation with inverse left translation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let L_g,R_g:Xp→L[ℂ]Xp extend the coefficient translations
f(s)↦α_g(f(g⁻¹*s)) and f(s)↦δ(g)•f(s*g⁻¹), respectively, where δ(g)=Measure.modularCharacter g
is embedded in ℂ. For g∈G and x∈Xp, star(R_g x)=L_(g⁻¹)(star(x)).
-/
theorem star_groupRightCompletion (g : G) (x : p.NonUnitalCompletion) :
    star (groupRightCompletion μ α p g x) = groupLeftCompletion μ α p g⁻¹ (star x) := by
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (groupRightCompletion μ α p g).continuous.star
    ((groupLeftCompletion μ α p g⁻¹).continuous.comp continuous_star) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.star_apply,
    groupRightCompletion_apply, ← map_star, groupLeftCompletion_apply]
  exact congrArg p.toNonUnitalCompletion (crossedStar_groupRight μ α g f)

/-- **Centralizer compatibility of completed group translations.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p
on Carrier μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for
its dense core map. Let L_g,R_g:Xp→L[ℂ]Xp extend the coefficient translations
f(s)↦α_g(f(g⁻¹*s)) and f(s)↦δ(g)•f(s*g⁻¹), respectively, where δ(g)=Measure.modularCharacter g
is embedded in ℂ. For g∈G and x,y∈Xp, (R_g x)*y=x*(L_g y).
-/
theorem groupCompletion_central (g : G) (x y : p.NonUnitalCompletion) :
    groupRightCompletion μ α p g x * y = x * groupLeftCompletion μ α p g y := by
  refine (p.denseRange_toNonUnitalCompletion).induction_on₂
    (p := fun u v : p.NonUnitalCompletion =>
      groupRightCompletion μ α p g u * v = u * groupLeftCompletion μ α p g v)
    ?_ ?_ x y
  · exact isClosed_eq
      (((groupRightCompletion μ α p g).continuous.comp continuous_fst).mul continuous_snd)
      (continuous_fst.mul ((groupLeftCompletion μ α p g).continuous.comp continuous_snd))
  · intro f h
    rw [groupRightCompletion_apply, groupLeftCompletion_apply, ← map_mul, ← map_mul]
    exact congrArg p.toNonUnitalCompletion (convolution_groupLeft μ α g f h).symm

end

end HaarTwistedCore
