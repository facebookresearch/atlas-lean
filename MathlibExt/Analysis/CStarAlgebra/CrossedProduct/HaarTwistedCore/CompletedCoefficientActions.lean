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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.SeminormCoefficientActions
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Coefficient actions on a C-star seminorm completion

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. These actions satisfy ‖L_a‖≤‖a‖ and ‖R_a‖≤‖a‖.
Their adjoint-exchange and centralizer laws are star(L_a x)=R_star(a)(star(x)) and (R_a
x)*y=x*(L_a y). The construction includes the zero seminorm and zero coefficient algebra.
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
variable (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α))

/-- **Completed left coefficient action.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. The bounded complex linear map
coefficientLeftCompletion μ α p a is L_a, determined by L_a(ιp(f))=ιp(s↦a*f(s)).
-/
def coefficientLeftCompletion (a : A) :
    p.NonUnitalCompletion →L[ℂ] p.NonUnitalCompletion :=
  ((LinearMap.ofClass p.toNonUnitalCompletion).comp (coefficientLeft μ α a)).extendOfNorm
    (LinearMap.ofClass p.toNonUnitalCompletion)

/-- **Completed right coefficient action.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. The bounded complex linear map
coefficientRightCompletion μ α p a is R_a, determined by R_a(ιp(f))=ιp(s↦f(s)*α_s(a)).
-/
def coefficientRightCompletion (a : A) :
    p.NonUnitalCompletion →L[ℂ] p.NonUnitalCompletion :=
  ((LinearMap.ofClass p.toNonUnitalCompletion).comp (coefficientRight μ α a)).extendOfNorm
    (LinearMap.ofClass p.toNonUnitalCompletion)

/-- **Left coefficient action on a dense completed class.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. For a∈A and f∈Carrier μ α, coefficientLeftCompletion μ α p a (ιp(f))=ιp(s↦a*f(s)).
-/
theorem coefficientLeftCompletion_apply (a : A) (f : Carrier μ α) :
    coefficientLeftCompletion μ α p a (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (coefficientLeft μ α a f) := by
  apply LinearMap.extendOfNorm_eq (p.denseRange_toNonUnitalCompletion)
  refine ⟨‖a‖, fun h => ?_⟩
  change ‖p.toNonUnitalCompletion (coefficientLeft μ α a h)‖ ≤
    ‖a‖ * ‖p.toNonUnitalCompletion h‖
  simpa only [CStarSeminorm.norm_toNonUnitalCompletion] using seminorm_coefficientLeft_le μ α p a h

/-- **Right coefficient action on a dense completed class.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. For a∈A and f∈Carrier μ α, coefficientRightCompletion μ α p a
(ιp(f))=ιp(s↦f(s)*α_s(a)).
-/
theorem coefficientRightCompletion_apply (a : A) (f : Carrier μ α) :
    coefficientRightCompletion μ α p a (p.toNonUnitalCompletion f) =
      p.toNonUnitalCompletion (coefficientRight μ α a f) := by
  apply LinearMap.extendOfNorm_eq (p.denseRange_toNonUnitalCompletion)
  refine ⟨‖a‖, fun h => ?_⟩
  change ‖p.toNonUnitalCompletion (coefficientRight μ α a h)‖ ≤
    ‖a‖ * ‖p.toNonUnitalCompletion h‖
  simpa only [CStarSeminorm.norm_toNonUnitalCompletion] using seminorm_coefficientRight_le μ α p a h

/-- **Pointwise bound for completed left coefficients.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. For a∈A and x∈Xp, ‖L_a x‖≤‖a‖‖x‖.
-/
theorem norm_coefficientLeftCompletion_apply_le (a : A) (x : p.NonUnitalCompletion) :
    ‖coefficientLeftCompletion μ α p a x‖ ≤ ‖a‖ * ‖x‖ := by
  apply LinearMap.norm_extendOfNorm_apply_le (p.denseRange_toNonUnitalCompletion) ‖a‖
  intro f
  change ‖p.toNonUnitalCompletion (coefficientLeft μ α a f)‖ ≤
    ‖a‖ * ‖p.toNonUnitalCompletion f‖
  simpa only [CStarSeminorm.norm_toNonUnitalCompletion] using seminorm_coefficientLeft_le μ α p a f

/-- **Pointwise bound for completed right coefficients.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. For a∈A and x∈Xp, ‖R_a x‖≤‖a‖‖x‖.
-/
theorem norm_coefficientRightCompletion_apply_le (a : A) (x : p.NonUnitalCompletion) :
    ‖coefficientRightCompletion μ α p a x‖ ≤ ‖a‖ * ‖x‖ := by
  apply LinearMap.norm_extendOfNorm_apply_le (p.denseRange_toNonUnitalCompletion) ‖a‖
  intro f
  change ‖p.toNonUnitalCompletion (coefficientRight μ α a f)‖ ≤
    ‖a‖ * ‖p.toNonUnitalCompletion f‖
  simpa only [CStarSeminorm.norm_toNonUnitalCompletion] using seminorm_coefficientRight_le μ α p a f

/-- **Operator norm of the completed left coefficient action.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. For a∈A, ‖coefficientLeftCompletion μ α p
a‖=‖L_a‖≤‖a‖.
-/
theorem norm_coefficientLeftCompletion_le (a : A) :
    ‖coefficientLeftCompletion μ α p a‖ ≤ ‖a‖ :=
  (coefficientLeftCompletion μ α p a).opNorm_le_bound (norm_nonneg a)
    (norm_coefficientLeftCompletion_apply_le μ α p a)

/-- **Operator norm of the completed right coefficient action.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. For a∈A, ‖coefficientRightCompletion μ α p
a‖=‖R_a‖≤‖a‖.
-/
theorem norm_coefficientRightCompletion_le (a : A) :
    ‖coefficientRightCompletion μ α p a‖ ≤ ‖a‖ :=
  (coefficientRightCompletion μ α p a).opNorm_le_bound (norm_nonneg a)
    (norm_coefficientRightCompletion_apply_le μ α p a)

/-- **Zero coefficient in the completed left action.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. The zero coefficient acts by L_0=0, the zero
bounded linear operator on Xp.
-/
@[simp]
theorem coefficientLeftCompletion_zero : coefficientLeftCompletion μ α p (0 : A) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientLeftCompletion μ α p 0).continuous continuous_const ?_) x
  funext f
  simp only [Function.comp_apply, coefficientLeftCompletion_apply, zero_apply]
  have h : coefficientLeft μ α (0 : A) f = 0 := by
    apply ext μ α
    intro s
    simp only [coefficientLeft_apply, zero_mul]
    rfl
  rw [h, map_zero]

/-- **Zero coefficient in the completed right action.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. The zero coefficient acts by R_0=0, the zero
bounded linear operator on Xp.
-/
@[simp]
theorem coefficientRightCompletion_zero : coefficientRightCompletion μ α p (0 : A) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientRightCompletion μ α p 0).continuous continuous_const ?_) x
  funext f
  simp only [Function.comp_apply, coefficientRightCompletion_apply, zero_apply]
  have h : coefficientRight μ α (0 : A) f = 0 := by
    apply ext μ α
    intro s
    simp only [coefficientRight_apply, α.apply_zero, mul_zero]
    rfl
  rw [h, map_zero]

/-- **Additivity of completed left coefficients.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. For a,b∈A, L_(a+b)=L_a+L_b.
-/
theorem coefficientLeftCompletion_add (a b : A) :
    coefficientLeftCompletion μ α p (a + b) =
      coefficientLeftCompletion μ α p a + coefficientLeftCompletion μ α p b := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientLeftCompletion μ α p (a + b)).continuous
    ((coefficientLeftCompletion μ α p a).continuous.add
      (coefficientLeftCompletion μ α p b).continuous) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.add_apply,
    coefficientLeftCompletion_apply, coefficientLeft_add, LinearMap.add_apply, map_add]

/-- **Additivity of completed right coefficients.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. For a,b∈A, R_(a+b)=R_a+R_b.
-/
theorem coefficientRightCompletion_add (a b : A) :
    coefficientRightCompletion μ α p (a + b) =
      coefficientRightCompletion μ α p a + coefficientRightCompletion μ α p b := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientRightCompletion μ α p (a + b)).continuous
    ((coefficientRightCompletion μ α p a).continuous.add
      (coefficientRightCompletion μ α p b).continuous) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.add_apply,
    coefficientRightCompletion_apply, coefficientRight_add, LinearMap.add_apply, map_add]

/-- **Complex scaling of completed left coefficients.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. For c∈ℂ and a∈A, L_(c•a)=c•L_a.
-/
theorem coefficientLeftCompletion_smul (c : ℂ) (a : A) :
    coefficientLeftCompletion μ α p (c • a) = c • coefficientLeftCompletion μ α p a := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientLeftCompletion μ α p (c • a)).continuous
    ((coefficientLeftCompletion μ α p a).continuous.const_smul c) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.smul_apply,
    coefficientLeftCompletion_apply, coefficientLeft_smul, LinearMap.smul_apply, map_smul]

/-- **Complex scaling of completed right coefficients.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. For c∈ℂ and a∈A, R_(c•a)=c•R_a.
-/
theorem coefficientRightCompletion_smul (c : ℂ) (a : A) :
    coefficientRightCompletion μ α p (c • a) = c • coefficientRightCompletion μ α p a := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientRightCompletion μ α p (c • a)).continuous
    ((coefficientRightCompletion μ α p a).continuous.const_smul c) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.smul_apply,
    coefficientRightCompletion_apply, coefficientRight_smul, LinearMap.smul_apply, map_smul]

/-- **Composition of completed left coefficients.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. For a,b∈A, L_(a*b)=L_a∘L_b.
-/
theorem coefficientLeftCompletion_mul (a b : A) :
    coefficientLeftCompletion μ α p (a * b) =
      (coefficientLeftCompletion μ α p a).comp (coefficientLeftCompletion μ α p b) := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientLeftCompletion μ α p (a * b)).continuous
    ((coefficientLeftCompletion μ α p a).continuous.comp
      (coefficientLeftCompletion μ α p b).continuous) ?_) x
  funext f
  simp only [Function.comp_apply,
    coefficientLeftCompletion_apply, coefficientLeft_mul, LinearMap.comp_apply]

/-- **Reversed composition of completed right coefficients.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. For a,b∈A, R_(a*b)=R_b∘R_a.
-/
theorem coefficientRightCompletion_mul (a b : A) :
    coefficientRightCompletion μ α p (a * b) =
      (coefficientRightCompletion μ α p b).comp (coefficientRightCompletion μ α p a) := by
  apply ContinuousLinearMap.ext
  intro x
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientRightCompletion μ α p (a * b)).continuous
    ((coefficientRightCompletion μ α p b).continuous.comp
      (coefficientRightCompletion μ α p a).continuous) ?_) x
  funext f
  simp only [Function.comp_apply,
    coefficientRightCompletion_apply, coefficientRight_mul, LinearMap.comp_apply]

/-- **Star exchanges the completed left and right coefficients.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. For a∈A and x∈Xp, star(L_a
x)=R_star(a)(star(x)).
-/
theorem star_coefficientLeftCompletion (a : A) (x : p.NonUnitalCompletion) :
    star (coefficientLeftCompletion μ α p a x) =
      coefficientRightCompletion μ α p (star a) (star x) := by
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientLeftCompletion μ α p a).continuous.star
    ((coefficientRightCompletion μ α p (star a)).continuous.comp continuous_star) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.star_apply,
    coefficientLeftCompletion_apply, ← map_star, coefficientRightCompletion_apply]
  exact congrArg p.toNonUnitalCompletion (crossedStar_coefficientLeft μ α a f)

/-- **Star exchanges the completed right and left coefficients.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. For a∈A and x∈Xp, star(R_a
x)=L_star(a)(star(x)).
-/
theorem star_coefficientRightCompletion (a : A) (x : p.NonUnitalCompletion) :
    star (coefficientRightCompletion μ α p a x) =
      coefficientLeftCompletion μ α p (star a) (star x) := by
  refine congrFun ((p.denseRange_toNonUnitalCompletion).equalizer
    (coefficientRightCompletion μ α p a).continuous.star
    ((coefficientLeftCompletion μ α p (star a)).continuous.comp continuous_star) ?_) x
  funext f
  simp only [Function.comp_apply, Pi.star_apply,
    coefficientRightCompletion_apply, ← map_star, coefficientLeftCompletion_apply]
  exact congrArg p.toNonUnitalCompletion (crossedStar_coefficientRight μ α a f)

/-- **Centralizer compatibility of completed coefficient actions.**

Let G be a locally compact Borel topological group with left Haar measure μ, A a nonunital
complex C-star algebra and α a point-norm action of G on A. For a C-star seminorm p on Carrier
μ α, write Xp=p.NonUnitalCompletion for its separated C-star completion and ιp for its dense
core map. Let L_a,R_a:Xp→L[ℂ]Xp be the extensions of f(s)↦a*f(s) and f(s)↦f(s)*α_s(a),
respectively, from dense coefficient classes. For a∈A and x,y∈Xp, (R_a x)*y=x*(L_a y).
-/
theorem coefficientCompletion_central (a : A) (x y : p.NonUnitalCompletion) :
    coefficientRightCompletion μ α p a x * y = x * coefficientLeftCompletion μ α p a y := by
  refine (p.denseRange_toNonUnitalCompletion).induction_on₂
    (p := fun u v : p.NonUnitalCompletion =>
      coefficientRightCompletion μ α p a u * v = u * coefficientLeftCompletion μ α p a v)
    ?_ ?_ x y
  · exact isClosed_eq
      (((coefficientRightCompletion μ α p a).continuous.comp continuous_fst).mul continuous_snd)
      (continuous_fst.mul ((coefficientLeftCompletion μ α p a).continuous.comp continuous_snd))
  · intro f h
    rw [coefficientRightCompletion_apply, coefficientLeftCompletion_apply, ← map_mul, ← map_mul]
    exact congrArg p.toNonUnitalCompletion (convolution_coefficientLeft μ α a f h).symm

end

end HaarTwistedCore
