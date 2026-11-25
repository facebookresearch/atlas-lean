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

public import MathlibExt.Analysis.CStarAlgebra.Weight.GNSLeftOperator
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Tactic.FunProp

/-!
# Adjoints of left multiplication in the weight GNS space

For an extended positive weight `φ` on a nonunital complex C-star algebra, the polarized pairing
on `n_φ` satisfies `P(a*x,y)=P(x,a* y)`. On the seminormed domain this is `⟨L_a x,y⟩=⟨x,L_(a*)
y⟩`.

After Hilbert completion, the bounded left operators satisfy `π(a*)=π(a)*`. The pairing and
adjoint identities use only the weight laws and C-star positivity; no faithful or
densely-defined weight is required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **Square difference for a left product.** In a nonunital complex C-star algebra,
`(a*x+y)*(a*x+y)-(a*x-y)*(a*x-y) = (x+a* y)*(x+a* y)-(x-a* y)*(x-a* y)` for `a,x,y : A`. -/
theorem leftSquare_difference_leftMul (a x y : A) :
    (leftSquare (a * x + y) : A) - (leftSquare (a * x - y) : A) =
      (leftSquare (x + star a * y) : A) - (leftSquare (x - star a * y) : A) := by
  simp only [leftSquare_difference, star_mul, star_star, mul_assoc]

/-- **Real adjoint identity for the weight polarization.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. put `R(x,y)=(q(x+y)-q(x-y))/4`. For `a : A` and `x,y ∈ n_φ`, `R(a*x,y)=R(x,a*
y)`. -/
theorem Weight.finiteSquarePolarRe_leftMul (φ : Weight A) (a : A)
    (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe (φ.finiteSquareLeftMul a x) y =
      φ.finiteSquarePolarRe x (φ.finiteSquareLeftMul (star a) y) := by
  have hraw :
      (leftSquare (((φ.finiteSquareLeftMul a x) + y : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare (((φ.finiteSquareLeftMul a x) - y : φ.finiteSquareSubmodule) : A) : A) =
      (leftSquare ((x + φ.finiteSquareLeftMul (star a) y : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare ((x - φ.finiteSquareLeftMul (star a) y : φ.finiteSquareSubmodule) : A) : A) := by
    change (leftSquare (a * (x : A) + (y : A)) : A) -
      (leftSquare (a * (x : A) - (y : A)) : A) =
      (leftSquare ((x : A) + star a * (y : A)) : A) -
      (leftSquare ((x : A) - star a * (y : A)) : A)
    exact leftSquare_difference_leftMul a (x : A) (y : A)
  have h := φ.finite_toReal_sub_eq_sub
    (leftSquare (((φ.finiteSquareLeftMul a x) + y : φ.finiteSquareSubmodule) : A))
    (leftSquare (((φ.finiteSquareLeftMul a x) - y : φ.finiteSquareSubmodule) : A))
    (leftSquare ((x + φ.finiteSquareLeftMul (star a) y : φ.finiteSquareSubmodule) : A))
    (leftSquare ((x - φ.finiteSquareLeftMul (star a) y : φ.finiteSquareSubmodule) : A))
    ((φ.finiteSquareLeftMul a x) + y).property ((φ.finiteSquareLeftMul a x) - y).property
    (x + φ.finiteSquareLeftMul (star a) y).property (x - φ.finiteSquareLeftMul (star a) y).property hraw
  dsimp only [Weight.finiteSquarePolarRe, Weight.finiteSquareValue]
  linarith [h]

/-- **Complex adjoint identity for the weight polarization.** Let `A` be a nonunital complex
C-star algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real
homogeneous weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x*
x)).toReal` for `x ∈ n_φ`. put `P(x,y)=finiteSquarePolarInner φ x y`. For `a : A` and `x,y ∈
n_φ`, `P(a*x,y)=P(x,a* y)`. -/
theorem Weight.finiteSquarePolarInner_leftMul (φ : Weight A) (a : A)
    (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarInner (φ.finiteSquareLeftMul a x) y =
      φ.finiteSquarePolarInner x (φ.finiteSquareLeftMul (star a) y) := by
  apply Complex.ext
  · change φ.finiteSquarePolarRe (φ.finiteSquareLeftMul a x) y =
      φ.finiteSquarePolarRe x (φ.finiteSquareLeftMul (star a) y)
    exact φ.finiteSquarePolarRe_leftMul a x y
  · change φ.finiteSquarePolarRe (Complex.I • φ.finiteSquareLeftMul a x) y =
      φ.finiteSquarePolarRe (Complex.I • x) (φ.finiteSquareLeftMul (star a) y)
    rw [← (φ.finiteSquareLeftMul a).map_smul Complex.I x]
    exact φ.finiteSquarePolarRe_leftMul a (Complex.I • x) y

/-- **Adjoint pairing of pre-GNS left operators.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. on the weight-seminormed type copy `PreGNS φ`, let `L_a` be left multiplication by `a`.
Then `⟨L_a x,y⟩=⟨x,L_(a*) y⟩` for all `x,y`. -/
theorem Weight.preGNSLeftMul_adjoint_pairing (φ : Weight A) (a : A) (x y : φ.PreGNS) :
    ⟪φ.preGNSLeftMul a x, y⟫_ℂ = ⟪x, φ.preGNSLeftMul (star a) y⟫_ℂ := by
  rw [φ.preGNS_inner, φ.preGNS_inner, φ.preGNSLeftMul_apply, φ.preGNSLeftMulLinear_apply,
    φ.preGNSLeftMul_apply, φ.preGNSLeftMulLinear_apply]
  exact φ.finiteSquarePolarInner_leftMul a (φ.preGNSLinearEquiv x) (φ.preGNSLinearEquiv y)

/-- **Adjoint law of completed left multiplication.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. if `π(a)=gnsLeftMul φ a` is the bounded extension of left
multiplication, then `π(a*)=π(a)*` for every `a : A`. -/
theorem Weight.gnsLeftMul_star (φ : Weight A) (a : A) :
    φ.gnsLeftMul (star a) = star (φ.gnsLeftMul a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff (φ.gnsLeftMul (star a)) (φ.gnsLeftMul a)).2 ?_
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
      change ⟪φ.gnsLeftMul (star a) (φ.toGNS x), φ.toGNS y⟫_ℂ =
        ⟪φ.toGNS x, φ.gnsLeftMul a (φ.toGNS y)⟫_ℂ
      rw [φ.gnsLeftMul_toGNS, φ.gnsLeftMul_toGNS, φ.toGNS_inner, φ.toGNS_inner]
      simpa only [star_star] using φ.preGNSLeftMul_adjoint_pairing (star a) x y

end

end CStarAlgebra.ScalarWeight
