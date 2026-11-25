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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CompletedGroupActions
public import Mathlib.Analysis.CStarAlgebra.Multiplier
public import Mathlib.Algebra.Star.Unitary

/-!
# Group unitaries in a C-star completion multiplier algebra

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. The group multiplier u_p(g) extends the left
action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g is viewed as a complex scalar. The map g↦u_p(g) is a group
homomorphism into the unitary group of 𝓜(ℂ,Xp), with star(u_p(g))=u_p(g⁻¹) and ‖u_p(g)‖≤1. The
statements also apply to the zero completion.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped MultiplierAlgebra

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

/-- **Double centralizer associated with a group element.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. The group multiplier u_p(g) extends the left
action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g is viewed as a complex scalar. These extended translations
define groupMultiplier μ α p g∈𝓜(ℂ,Xp).
-/
def groupMultiplier (g : G) : 𝓜(ℂ, p.NonUnitalCompletion) where
  fst := groupLeftCompletion μ α p g
  snd := groupRightCompletion μ α p g
  central := groupCompletion_central μ α p g

/-- **Left group multiplier on dense classes.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. For g∈G and f∈Carrier μ α, (groupMultiplier μ α p
g).fst(ιp(f))=ιp(s↦α_g(f(g⁻¹*s))).
-/
theorem groupMultiplier_fst_apply (g : G) (f : Carrier μ α) :
    (groupMultiplier μ α p g).fst (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (groupLeft μ α g f) :=
  groupLeftCompletion_apply μ α p g f

/-- **Right group multiplier on dense classes.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. For g∈G and f∈Carrier μ α, (groupMultiplier μ α p
g).snd(ιp(f))=ιp(s↦δ(g)•f(s*g⁻¹)), where δ(g)=Measure.modularCharacter g is a positive real
scalar embedded in ℂ.
-/
theorem groupMultiplier_snd_apply (g : G) (f : Carrier μ α) :
    (groupMultiplier μ α p g).snd (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (groupRight μ α g f) :=
  groupRightCompletion_apply μ α p g f

/-- **Group homomorphism into completion multipliers.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. The group multiplier u_p(g) extends the left
action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g is viewed as a complex scalar. The homomorphism
groupMultiplierHom μ α p:G→𝓜(ℂ,Xp) satisfies u_p(gh)=u_p(g)u_p(h) and u_p(1)=1.
-/
def groupMultiplierHom : G →* 𝓜(ℂ, p.NonUnitalCompletion) where
  toFun := groupMultiplier μ α p
  map_one' := by
    apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
    apply Prod.ext
    · exact groupLeftCompletion_one μ α p
    · exact groupRightCompletion_one μ α p
  map_mul' g h := by
    apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
    apply Prod.ext
    · exact groupLeftCompletion_mul μ α p g h
    · exact groupRightCompletion_mul μ α p g h

/-- **Value of the group multiplier homomorphism.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. The group multiplier u_p(g) extends the left
action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g is viewed as a complex scalar. For g∈G, groupMultiplierHom μ α
p g=groupMultiplier μ α p g=u_p(g).
-/
@[simp]
theorem groupMultiplierHom_apply (g : G) :
    groupMultiplierHom μ α p g = groupMultiplier μ α p g := rfl

/-- **Adjoint of a group multiplier.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. The group multiplier u_p(g) extends the left
action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g is viewed as a complex scalar. The adjoint satisfies
star(groupMultiplier μ α p g)=groupMultiplier μ α p g⁻¹.
-/
theorem star_groupMultiplier (g : G) :
    star (groupMultiplier μ α p g) = groupMultiplier μ α p g⁻¹ := by
  apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
  apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro x
  · change star (groupRightCompletion μ α p g (star x)) = groupLeftCompletion μ α p g⁻¹ x
    simpa only [star_star] using star_groupRightCompletion μ α p g (star x)
  · change star (groupLeftCompletion μ α p g (star x)) = groupRightCompletion μ α p g⁻¹ x
    simpa only [star_star] using star_groupLeftCompletion μ α p g (star x)

/-- **Unitarity of completed group translations.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. The group multiplier u_p(g) extends the left
action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g is viewed as a complex scalar. For g∈G, u_p(g) is unitary in
𝓜(ℂ,Xp): star(u_p(g))*u_p(g)=u_p(g)*star(u_p(g))=1. This includes Xp=0.
-/
theorem groupMultiplier_mem_unitary (g : G) :
    groupMultiplier μ α p g ∈ unitary 𝓜(ℂ, p.NonUnitalCompletion) := by
  change star (groupMultiplier μ α p g) * groupMultiplier μ α p g = 1 ∧
    groupMultiplier μ α p g * star (groupMultiplier μ α p g) = 1
  simp only [star_groupMultiplier]
  constructor
  · change groupMultiplierHom μ α p g⁻¹ * groupMultiplierHom μ α p g = 1
    rw [← map_mul, inv_mul_cancel, map_one]
  · change groupMultiplierHom μ α p g * groupMultiplierHom μ α p g⁻¹ = 1
    rw [← map_mul, mul_inv_cancel, map_one]

/-- **Unitary-valued group multiplier representation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. The group multiplier u_p(g) extends the left
action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g is viewed as a complex scalar. The map
groupUnitaryMultiplierHom μ α p is a group homomorphism G→unitary(𝓜(ℂ,Xp)), assigning the
unitary u_p(g) to g.
-/
def groupUnitaryMultiplierHom : G →* unitary 𝓜(ℂ, p.NonUnitalCompletion) where
  toFun g := ⟨groupMultiplierHom μ α p g, groupMultiplier_mem_unitary μ α p g⟩
  map_one' := Subtype.ext (map_one (groupMultiplierHom μ α p))
  map_mul' g h := Subtype.ext (map_mul (groupMultiplierHom μ α p) g h)

/-- **Multiplier underlying the unitary group map.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. The group multiplier u_p(g) extends the left
action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g is viewed as a complex scalar. The inclusion of
groupUnitaryMultiplierHom μ α p g into 𝓜(ℂ,Xp) is groupMultiplier μ α p g.
-/
@[simp]
theorem groupUnitaryMultiplierHom_coe (g : G) :
    ((groupUnitaryMultiplierHom μ α p g : unitary 𝓜(ℂ, p.NonUnitalCompletion)) :
      𝓜(ℂ, p.NonUnitalCompletion)) = groupMultiplier μ α p g := rfl

/-- **Uniform norm bound for group multipliers.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star
completion and ιp its dense coefficient map. The group multiplier u_p(g) extends the left
action L_g f(s)=α_g(f(g⁻¹*s)) and the right action R_g f(s)=δ(g)•f(s*g⁻¹), where
δ(g)=Measure.modularCharacter g is viewed as a complex scalar. For every g∈G, ‖groupMultiplier
μ α p g‖≤1; the inequality remains valid for the zero completion.
-/
theorem norm_groupMultiplier_le_one (g : G) : ‖groupMultiplier μ α p g‖ ≤ 1 := by
  rw [← DoubleCentralizer.norm_fst]
  apply (groupLeftCompletion μ α p g).opNorm_le_bound zero_le_one
  intro x
  simpa only [one_mul] using (norm_groupLeftCompletion_apply μ α p g x).le

end

end HaarTwistedCore
