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

public import MathlibExt.Analysis.CStarAlgebra.Weight.PreInnerProduct
public import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Weight seminorm and faithful pre-GNS norm

For an extended positive weight on a nonunital complex C-star algebra, the polarized form on
`n_φ = {x : φ(x* x) < ∞}` gives the seminorm `‖x‖_φ=√((φ(x* x)).toReal)` and distance
`d_φ(x,y)=‖x-y‖_φ`. The space `PreGNS φ` is a type copy of `n_φ` carrying this seminorm and
inner product, rather than the ambient norm inherited from `A`.

If the weight is faithful on positive elements, the form is definite and this seminorm is a
norm. For a general weight nonzero null vectors are allowed; completeness of the domain is not
assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **Weight seminormed additive group.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. the
type copy `PreGNS φ` of `n_φ` has seminorm `‖x‖_φ=√q(x)` and distance `d_φ(x,y)=√q(x-y)`,
which may vanish on nonzero vectors. -/
instance Weight.preGNSSeminormedAddCommGroup (φ : Weight A) : SeminormedAddCommGroup φ.PreGNS :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := φ.preGNSPreInnerProduct)

/-- **Seminormed GNS inner-product space.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. For
`x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i • x,y)`. `PreGNS φ`
carries the complex inner product `P` and its induced seminorm; the form may be degenerate. -/
instance Weight.preGNSInnerProductSpace (φ : Weight A) : InnerProductSpace ℂ φ.PreGNS :=
  InnerProductSpace.ofCore φ.preGNSPreInnerProduct

/-- **Pre-GNS inner product under the domain identification.** Let `A` be a nonunital complex
C-star algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real
homogeneous weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x*
x)).toReal` for `x ∈ n_φ`. For `x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and
`P(x,y)=R(x,y)+i R(i • x,y)`. if `e=preGNSLinearEquiv φ : PreGNS φ ≃ₗ[ℂ] n_φ`, then
`⟨x,y⟩=P(e(x),e(y))` for pre-GNS vectors `x,y`. -/
@[simp]
theorem Weight.preGNS_inner (φ : Weight A) (x y : φ.PreGNS) :
    ⟪x, y⟫_ℂ = φ.finiteSquarePolarInner (φ.preGNSLinearEquiv x) (φ.preGNSLinearEquiv y) :=
  rfl

/-- **Square-root formula for the weight seminorm.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. if `e=preGNSLinearEquiv φ`, then `‖x‖_φ=√q(e(x))` for `x : PreGNS φ`. -/
theorem Weight.preGNS_norm (φ : Weight A) (x : φ.PreGNS) :
    ‖x‖ = Real.sqrt (φ.finiteSquareValue (φ.preGNSLinearEquiv x)) := by
  change Real.sqrt (RCLike.re (φ.finiteSquarePolarInner
    (φ.preGNSLinearEquiv x) (φ.preGNSLinearEquiv x))) =
      Real.sqrt (φ.finiteSquareValue (φ.preGNSLinearEquiv x))
  rw [φ.finiteSquarePolarInner_self, RCLike.ofReal_re]

/-- **Square of the pre-GNS seminorm.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. if
`e=preGNSLinearEquiv φ`, then `‖x‖_φ²=q(e(x))=(φ(e(x)* e(x))).toReal` for `x : PreGNS φ`. -/
theorem Weight.preGNS_norm_sq (φ : Weight A) (x : φ.PreGNS) :
    ‖x‖ ^ 2 = φ.finiteSquareValue (φ.preGNSLinearEquiv x) := by
  rw [φ.preGNS_norm]
  exact Real.sq_sqrt (φ.finiteSquareValue_nonneg _)

/-- **Definiteness of a faithful weight pairing.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. assume `φ(a)=0 → a=0` for every positive `a : A`. Then `⟨x,x⟩=0` implies `x=0` for every
`x : PreGNS φ`. -/
theorem Weight.preGNS_definite (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (x : φ.PreGNS) (hx : φ.preGNSPreInnerProduct.inner x x = 0) : x = 0 := by
  let y : φ.finiteSquareSubmodule := φ.preGNSLinearEquiv x
  have hreal := congrArg (fun z : ℂ => RCLike.re z) hx
  change RCLike.re (φ.finiteSquarePolarInner y y) = RCLike.re (0 : ℂ) at hreal
  rw [φ.finiteSquarePolarInner_self, RCLike.ofReal_re, map_zero] at hreal
  have hfinite : φ.value (leftSquare (y : A)) < ⊤ := y.property
  change (φ.value (leftSquare (y : A))).toReal = 0 at hreal
  have hvalue : φ.value (leftSquare (y : A)) = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).1 hreal).resolve_right hfinite.ne
  have hsquare : star (y : A) * (y : A) = 0 := hφ (leftSquare (y : A)) hvalue
  have hy : (y : A) = 0 := star_mul_self_eq_zero.mp hsquare
  apply φ.preGNSLinearEquiv.injective
  rw [map_zero]
  apply Subtype.ext
  exact hy

/-- **Definite inner-product core of a faithful weight.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. For `x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i •
x,y)`. under faithfulness `φ(a)=0 → a=0` on positive elements, `faithfulPreGNSCore φ` is the
definite complex inner-product core with pairing `P` on `PreGNS φ`. -/
@[instance_reducible]
def Weight.faithfulPreGNSCore (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    InnerProductSpace.Core ℂ φ.PreGNS where
  __ := φ.preGNSPreInnerProduct
  definite x hx := φ.preGNS_definite hφ x hx

/-- **Pre-GNS normed group for a faithful weight.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. if `φ(a)=0 → a=0` for all positive `a`, `PreGNS φ` is a normed additive commutative
group with norm `√q(x)`; the norm is the same weight seminorm with definiteness proved. -/
@[instance_reducible]
def Weight.faithfulPreGNSNormedAddCommGroup (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    NormedAddCommGroup φ.PreGNS :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := φ.faithfulPreGNSCore hφ)

end

end CStarAlgebra.ScalarWeight
