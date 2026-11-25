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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CompletedCoefficientActions
public import Mathlib.Analysis.CStarAlgebra.Multiplier

/-!
# Coefficient multipliers of a C-star seminorm completion

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. Let p be a C-star seminorm on the
twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star completion and ιp its
dense coefficient map. For a∈A, the multiplier j_p(a) has left and right components extending
L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). The map a↦j_p(a) is a nonunital complex star
homomorphism A→𝓜(ℂ,Xp) and satisfies ‖j_p(a)‖≤‖a‖.
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
variable (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α))

/-- **Double centralizer associated with a coefficient.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. Let p be a C-star seminorm on the
twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star completion and ιp its
dense coefficient map. For a∈A, the multiplier j_p(a) has left and right components extending
L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). The pair of extended bounded complex linear maps is
coefficientMultiplier μ α p a∈𝓜(ℂ,Xp).
-/
def coefficientMultiplier (a : A) : 𝓜(ℂ, p.NonUnitalCompletion) where
  fst := coefficientLeftCompletion μ α p a
  snd := coefficientRightCompletion μ α p a
  central := coefficientCompletion_central μ α p a

/-- **Left coefficient multiplier on dense classes.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. Let p be a C-star seminorm on the
twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star completion and ιp its
dense coefficient map. For a∈A and f∈Carrier μ α, (coefficientMultiplier μ α p
a).fst(ιp(f))=ιp(s↦a*f(s)).
-/
theorem coefficientMultiplier_fst_apply (a : A) (f : Carrier μ α) :
    (coefficientMultiplier μ α p a).fst (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (coefficientLeft μ α a f) :=
  coefficientLeftCompletion_apply μ α p a f

/-- **Right coefficient multiplier on dense classes.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. Let p be a C-star seminorm on the
twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star completion and ιp its
dense coefficient map. For a∈A and f∈Carrier μ α, (coefficientMultiplier μ α p
a).snd(ιp(f))=ιp(s↦f(s)*α_s(a)).
-/
theorem coefficientMultiplier_snd_apply (a : A) (f : Carrier μ α) :
    (coefficientMultiplier μ α p a).snd (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (coefficientRight μ α a f) :=
  coefficientRightCompletion_apply μ α p a f

/-- **Coefficient homomorphism into the multiplier algebra.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. Let p be a C-star seminorm on the
twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star completion and ιp its
dense coefficient map. For a∈A, the multiplier j_p(a) has left and right components extending
L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). The map coefficientMultiplierHom μ α p:A→𝓜(ℂ,Xp) is
a nonunital complex star homomorphism.
-/
def coefficientMultiplierHom : A →⋆ₙₐ[ℂ] 𝓜(ℂ, p.NonUnitalCompletion) where
  toFun := coefficientMultiplier μ α p
  map_zero' := by
    apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
    apply Prod.ext
    · exact coefficientLeftCompletion_zero μ α p
    · exact coefficientRightCompletion_zero μ α p
  map_add' a b := by
    apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
    apply Prod.ext
    · exact coefficientLeftCompletion_add μ α p a b
    · exact coefficientRightCompletion_add μ α p a b
  map_smul' c a := by
    apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
    apply Prod.ext
    · exact coefficientLeftCompletion_smul μ α p c a
    · exact coefficientRightCompletion_smul μ α p c a
  map_mul' a b := by
    apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
    apply Prod.ext
    · exact coefficientLeftCompletion_mul μ α p a b
    · exact coefficientRightCompletion_mul μ α p a b
  map_star' a := by
    apply DoubleCentralizer.ext ℂ p.NonUnitalCompletion
    apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro x
    · change coefficientLeftCompletion μ α p (star a) x =
        star (coefficientRightCompletion μ α p a (star x))
      simpa only [star_star] using (star_coefficientRightCompletion μ α p a (star x)).symm
    · change coefficientRightCompletion μ α p (star a) x =
        star (coefficientLeftCompletion μ α p a (star x))
      simpa only [star_star] using (star_coefficientLeftCompletion μ α p a (star x)).symm

/-- **Value of the coefficient multiplier homomorphism.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. Let p be a C-star seminorm on the
twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star completion and ιp its
dense coefficient map. For a∈A, the multiplier j_p(a) has left and right components extending
L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). For every a∈A, coefficientMultiplierHom μ α p
a=coefficientMultiplier μ α p a=j_p(a).
-/
@[simp]
theorem coefficientMultiplierHom_apply (a : A) :
    coefficientMultiplierHom μ α p a = coefficientMultiplier μ α p a := rfl

/-- **Norm bound for coefficient multipliers.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. Let p be a C-star seminorm on the
twisted core Carrier μ α, Xp=p.NonUnitalCompletion its separated C-star completion and ιp its
dense coefficient map. For a∈A, the multiplier j_p(a) has left and right components extending
L_a f(s)=a*f(s) and R_a f(s)=f(s)*α_s(a). The multiplier norm satisfies ‖coefficientMultiplier
μ α p a‖≤‖a‖ for every a∈A.
-/
theorem norm_coefficientMultiplier_le (a : A) : ‖coefficientMultiplier μ α p a‖ ≤ ‖a‖ := by
  rw [← DoubleCentralizer.norm_fst]
  exact norm_coefficientLeftCompletion_le μ α p a

end

end HaarTwistedCore
