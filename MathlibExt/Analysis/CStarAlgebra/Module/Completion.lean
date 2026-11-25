/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Normed.Module.Completion

import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.Ring

/-!
# Inner-product data on the genuine completion of a pre-Hilbert C-star module

The input module is definite and uses its given normed-space dictionaries.
The carrier and norm below are stock UniformSpace.Completion. The linear
inner variable is completed first and the conjugate-linear variable second.
No completed CStarModule instance, coefficient action or tensor model is
assumed or installed by this first data leaf.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace CStarModule

universe uA uE

variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [SMul A E] [CStarModule A E]

/--
Let A be a possibly nonunital complex C*-algebra with a star-compatible partial order. Let E be
a normed complex inner-product A-module with its compatible coefficient action, and let Ē be its
norm completion.

The A-valued inner product on E extends to a continuous sesquilinear form on Ē × Ē,
conjugate-linear in the first argument and linear in the second.
-/
def completionInnerSL :
    UniformSpace.Completion E →L⋆[ℂ] UniformSpace.Completion E →L[ℂ] A :=
  ((((CStarModule.innerSL (A := A) (E := E)).flip).fromCompletion).flip).fromCompletion

/--
Let A be a possibly nonunital complex C*-algebra with a star-compatible partial order. Let E be
a normed complex inner-product A-module with its compatible coefficient action, and let Ē be its
norm completion.

The extended inner product of the canonical images of x, y ∈ E is the original A-valued inner
product of x and y.
-/
@[simp]
theorem completionInnerSL_apply_coe_coe (x y : E) :
    completionInnerSL (A := A) (x : UniformSpace.Completion E)
      (y : UniformSpace.Completion E) = inner A x y := by
  rw [completionInnerSL, ContinuousLinearMap.fromCompletion_apply_coe]
  change ((CStarModule.innerSL (A := A) (E := E)).flip).fromCompletion
      (y : UniformSpace.Completion E) x = inner A x y
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  change CStarModule.innerSL (A := A) x y = inner A x y
  exact CStarModule.innerSL_apply

/--
Let A be a possibly nonunital complex C*-algebra with a star-compatible partial order. Let E be
a normed complex inner-product A-module with its compatible coefficient action, and let Ē be its
norm completion.

The extended A-valued inner product is jointly continuous on Ē × Ē.
-/
@[continuity, fun_prop]
theorem continuous_completionInnerSL :
    Continuous fun p : UniformSpace.Completion E × UniformSpace.Completion E =>
      completionInnerSL (A := A) p.1 p.2 :=
  ((completionInnerSL (A := A) (E := E)).continuous.comp continuous_fst).clm_apply
    continuous_snd


/-- The actual input coefficient action as a bounded complex-linear map. -/
private def completionInputCoeffCLM (a : A) : E →L[ℂ] E := by
  have heq (u v : E) (h : ∀ z : E, inner A z u = inner A z v) : u = v := by
    apply sub_eq_zero.mp
    apply (CStarModule.inner_self (A := A) (x := u - v)).mp
    rw [CStarModule.inner_sub_right, h (u - v), sub_self]
  let f : E →ₗ[ℂ] E :=
    { toFun := fun x => a • x
      map_add' := by
        intro x y
        apply heq
        intro w
        simp only [CStarModule.inner_op_smul_right, CStarModule.inner_add_right, mul_add]
      map_smul' := by
        intro c x
        apply heq
        intro w
        simp only [CStarModule.inner_op_smul_right,
          CStarModule.inner_smul_right_complex, mul_smul_comm, RingHom.id_apply] }
  exact f.mkContinuous ‖a‖ fun x => by
    change ‖a • x‖ ≤ ‖a‖ * ‖x‖
    apply (sq_le_sq₀ (norm_nonneg (a • x))
      (mul_nonneg (norm_nonneg a) (norm_nonneg x))).mp
    rw [CStarModule.norm_sq_eq (A := A) (x := a • x),
      CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right]
    calc
      ‖a * inner A x x * star a‖ ≤ ‖a * inner A x x‖ * ‖star a‖ :=
        norm_mul_le _ _
      _ ≤ (‖a‖ * ‖inner A x x‖) * ‖star a‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = (‖a‖ * ‖x‖) ^ 2 := by
        rw [norm_star, ← CStarModule.norm_sq_eq (A := A) (x := x)]
        ring

omit [StarOrderedRing A] in
/--
Let A be a possibly nonunital complex C*-algebra with a partial order. Let E be a normed complex
inner-product A-module with its compatible coefficient action, and let Ē be its norm completion.

For each a ∈ A, the coefficient action x ↦ a • x on E is uniformly continuous.
-/
theorem completionInputUniformContinuousConstSMul : UniformContinuousConstSMul A E := by
  constructor
  intro a
  change UniformContinuous (completionInputCoeffCLM (A := A) (E := E) a)
  exact (completionInputCoeffCLM (A := A) (E := E) a).uniformContinuous

omit [StarOrderedRing A] in
/--
Let A be a possibly nonunital complex C*-algebra with a partial order. Let E be a normed complex
inner-product A-module with its compatible coefficient action, and let Ē be its norm completion.

For a ∈ A and x ∈ E, the canonical image of a • x in Ē equals a • the canonical image of x.
-/
@[simp]
theorem coe_completion_coeff_smul (a : A) (x : E) :
    (↑(a • x) : UniformSpace.Completion E) =
      a • (x : UniformSpace.Completion E) := by
  let : UniformContinuousConstSMul A E :=
    completionInputUniformContinuousConstSMul (A := A) (E := E)
  exact UniformSpace.Completion.coe_smul a x

/--
Let A be a possibly nonunital complex C*-algebra with a star-compatible partial order. Let E be
a normed complex inner-product A-module with its compatible coefficient action, and let Ē be its
norm completion.

For x, y ∈ Ē, conjugating their extended inner product exchanges the two arguments.
-/
theorem completionInnerSL_star (x y : UniformSpace.Completion E) :
    star (completionInnerSL (A := A) x y) = completionInnerSL (A := A) y x := by
  have hc := continuous_completionInnerSL (A := A) (E := E)
  have hs : Continuous fun p : UniformSpace.Completion E × UniformSpace.Completion E =>
      star (completionInnerSL (A := A) p.1 p.2) :=
    continuous_star.comp hc
  have ht : Continuous fun p : UniformSpace.Completion E × UniformSpace.Completion E =>
      completionInnerSL (A := A) p.2 p.1 :=
    hc.comp (continuous_snd.prodMk continuous_fst)
  refine UniformSpace.Completion.induction_on₂ x y (isClosed_eq hs ht) ?_
  intro u v
  rw [completionInnerSL_apply_coe_coe, completionInnerSL_apply_coe_coe]
  exact CStarModule.star_inner u v

/--
Let A be a possibly nonunital complex C*-algebra with a star-compatible partial order. Let E be
a normed complex inner-product A-module with its compatible coefficient action, and let Ē be its
norm completion.

For x ∈ Ē, the extended inner product ⟨x, x⟩ is nonnegative in A.
-/
theorem completionInnerSL_self_nonneg (x : UniformSpace.Completion E) :
    0 ≤ completionInnerSL (A := A) x x := by
  have hc : Continuous fun y : UniformSpace.Completion E =>
      completionInnerSL (A := A) y y :=
    (continuous_completionInnerSL (A := A) (E := E)).comp
      (continuous_id.prodMk continuous_id)
  refine UniformSpace.Completion.induction_on x
    ((CStarAlgebra.isClosed_nonneg (A := A)).preimage hc) ?_
  intro u
  rw [completionInnerSL_apply_coe_coe]
  exact CStarModule.inner_self_nonneg

/--
Let A be a possibly nonunital complex C*-algebra with a star-compatible partial order. Let E be
a normed complex inner-product A-module with its compatible coefficient action, and let Ē be its
norm completion.

For x ∈ Ē, the completion norm satisfies ‖x‖ = sqrt(‖⟨x, x⟩‖).
-/
theorem norm_completion_eq_sqrt_norm_completionInnerSL (x : UniformSpace.Completion E) :
    ‖x‖ = √‖completionInnerSL (A := A) x x‖ := by
  have hc : Continuous fun y : UniformSpace.Completion E =>
      completionInnerSL (A := A) y y :=
    (continuous_completionInnerSL (A := A) (E := E)).comp
      (continuous_id.prodMk continuous_id)
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq continuous_norm
      (Real.continuous_sqrt.comp (continuous_norm.comp hc))) ?_
  intro u
  rw [completionInnerSL_apply_coe_coe, UniformSpace.Completion.norm_coe]
  exact CStarModule.norm_eq_sqrt_norm_inner_self (A := A) u

/--
Let A be a possibly nonunital complex C*-algebra with a star-compatible partial order. Let E be
a normed complex inner-product A-module with its compatible coefficient action, and let Ē be its
norm completion.

For x ∈ Ē, the extended inner product ⟨x, x⟩ is zero if and only if x = 0.
-/
theorem completionInnerSL_self_eq_zero_iff (x : UniformSpace.Completion E) :
    completionInnerSL (A := A) x x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply norm_eq_zero.mp
    rw [norm_completion_eq_sqrt_norm_completionInnerSL (A := A) (E := E),
      hx, norm_zero, Real.sqrt_zero]
  · rintro rfl
    exact (completionInnerSL (A := A) (E := E) 0).map_zero

/--
Let A be a possibly nonunital complex C*-algebra with a star-compatible partial order. Let E be
a normed complex inner-product A-module with its compatible coefficient action, and let Ē be its
norm completion.

For x, y ∈ Ē and a ∈ A, the extended inner product satisfies ⟨x, a • y⟩ = a * ⟨x, y⟩.
-/
theorem completionInnerSL_coeff_smul_right (a : A) (x y : UniformSpace.Completion E) :
    completionInnerSL (A := A) x (a • y) = a * completionInnerSL (A := A) x y := by
  have hc := continuous_completionInnerSL (A := A) (E := E)
  have hl : Continuous fun p : UniformSpace.Completion E × UniformSpace.Completion E =>
      completionInnerSL (A := A) p.1 (a • p.2) :=
    hc.comp (continuous_fst.prodMk ((continuous_const_smul a).comp continuous_snd))
  have hr : Continuous fun p : UniformSpace.Completion E × UniformSpace.Completion E =>
      a * completionInnerSL (A := A) p.1 p.2 :=
    continuous_const.mul hc
  refine UniformSpace.Completion.induction_on₂ x y (isClosed_eq hl hr) ?_
  intro u v
  rw [← coe_completion_coeff_smul a v,
    completionInnerSL_apply_coe_coe, completionInnerSL_apply_coe_coe]
  exact CStarModule.inner_op_smul_right

/--
Let A be a possibly nonunital complex C*-algebra with a star-compatible partial order. Let E be
a normed complex inner-product A-module with its compatible coefficient action, and let Ē be its
norm completion.

The completion Ē is an inner-product C*-module over A with its completion norm, extended
coefficient action and extended A-valued inner product.
-/
@[instance_reducible]
def completionCStarModule : CStarModule A (UniformSpace.Completion E) where
  inner := fun x y => completionInnerSL (A := A) x y
  inner_add_right := by
    intro x y z
    exact (completionInnerSL (A := A) x).map_add y z
  inner_self_nonneg := by
    intro x
    exact completionInnerSL_self_nonneg (A := A) (E := E) x
  inner_self := by
    intro x
    exact completionInnerSL_self_eq_zero_iff (A := A) (E := E) x
  inner_op_smul_right := by
    intro a x y
    exact completionInnerSL_coeff_smul_right (A := A) (E := E) a x y
  inner_smul_right_complex := by
    intro c x y
    exact (completionInnerSL (A := A) x).map_smul c y
  star_inner := by
    intro x y
    exact completionInnerSL_star (A := A) (E := E) x y
  norm_eq_sqrt_norm_inner_self := by
    intro x
    exact norm_completion_eq_sqrt_norm_completionInnerSL (A := A) (E := E) x

/--
Let A be a possibly nonunital complex C*-algebra with a star-compatible partial order. Let E be
a normed complex inner-product A-module with its compatible coefficient action, and let Ē be its
norm completion.

The inner product of the completed C*-module is the continuous sesquilinear extension of the
inner product on E.
-/
theorem completionCStarModule_inner (x y : UniformSpace.Completion E) :
    letI : CStarModule A (UniformSpace.Completion E) :=
      completionCStarModule (A := A) (E := E)
    inner A x y = completionInnerSL (A := A) x y := rfl

/--
Let A be a possibly nonunital complex C*-algebra with a star-compatible partial order. Let E be
a normed complex inner-product A-module with its compatible coefficient action, and let Ē be its
norm completion.

In the completed C*-module, the inner product of the canonical images of x, y ∈ E is their
original inner product.
-/
@[simp]
theorem completionCStarModule_inner_coe_coe (x y : E) :
    letI : CStarModule A (UniformSpace.Completion E) :=
      completionCStarModule (A := A) (E := E)
    inner A (x : UniformSpace.Completion E) (y : UniformSpace.Completion E) = inner A x y := by
  exact completionInnerSL_apply_coe_coe x y

end CStarModule
