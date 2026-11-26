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

public import MathlibExt.Analysis.CStarAlgebra.Weight.FiniteValueRelations
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# The polarized form of a positive weight

For an extended positive weight `φ` on a nonunital complex C-star algebra, put `n_φ={x : φ(x*
x)<∞}`, `q(x)=(φ(x* x)).toReal` and `R(x,y)=(q(x+y)-q(x-y))/4`. The complex polarization
`P(x,y)=R(x,y)+i R(i • x,y)` is Hermitian, additive in its first argument and satisfies `P(c •
x,y)=conj(c) P(x,y)`.

Its diagonal is `P(x,x)=q(x) ≥ 0`. A type copy `PreGNS φ` of `n_φ` carries the additive and
complex-linear structures together with this positive semidefinite form. Faithfulness is not
needed; in particular the form may have nonzero null vectors.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- **Cross terms of an adjoint square difference.** For `x,y` in a nonunital complex C-star
algebra, `(x+y)*(x+y)-(x-y)*(x-y)=2 • (x* y+y* x)` as an equality in the algebra. -/
theorem leftSquare_difference (x y : A) :
    (leftSquare (x + y) : A) - (leftSquare (x - y) : A) =
      (star x * y + star y * x) + (star x * y + star y * x) := by
  simp only [leftSquare, star_add, star_sub, add_mul, mul_add, sub_mul, mul_sub]
  abel

/-- **Weight square value at zero.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`.
`q(0)=0`. -/
theorem Weight.finiteSquareValue_zero (φ : Weight A) : φ.finiteSquareValue 0 = 0 := by
  have hzero : leftSquare (0 : A) = positiveZero A := by
    apply Subtype.ext
    simp only [leftSquare, positiveZero, star_zero, zero_mul]
  change (φ.value (leftSquare (0 : A))).toReal = 0
  rw [hzero, φ.zero_value, ENNReal.toReal_zero]

/-- **Nonnegativity of finite square values.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. `0 ≤ q(x)` for every `x ∈ n_φ`. -/
theorem Weight.finiteSquareValue_nonneg (φ : Weight A) (x : φ.finiteSquareSubmodule) :
    0 ≤ φ.finiteSquareValue x :=
  ENNReal.toReal_nonneg

/-- **Weight square unchanged by negation.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. `q(-x)=q(x)` for every `x ∈ n_φ`. -/
theorem Weight.finiteSquareValue_neg (φ : Weight A) (x : φ.finiteSquareSubmodule) :
    φ.finiteSquareValue (-x) = φ.finiteSquareValue x := by
  have hneg : leftSquare (-(x : A)) = leftSquare (x : A) := by
    apply Subtype.ext
    simp only [leftSquare, star_neg, neg_mul, mul_neg, neg_neg]
  change (φ.value (leftSquare (-(x : A)))).toReal = (φ.value (leftSquare (x : A))).toReal
  rw [hneg]

/-- **Quadratic scaling of the weight square.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. `q(c • x)=‖c‖² q(x)` for every `c : ℂ` and `x ∈ n_φ`, including zero scalars. -/
theorem Weight.finiteSquareValue_smul (φ : Weight A) (c : ℂ) (x : φ.finiteSquareSubmodule) :
    φ.finiteSquareValue (c • x) = ‖c‖ ^ 2 * φ.finiteSquareValue x := by
  have hsquare : leftSquare (c • (x : A)) =
      positiveSmul (NNReal.mk (‖c‖ ^ 2) (sq_nonneg ‖c‖)) (leftSquare (x : A)) :=
    leftSquare_smul c (x : A)
  have hvalue := congrArg (fun z : PositiveElement A => (φ.value z).toReal) hsquare
  change (φ.value (leftSquare (c • (x : A)))).toReal =
    ‖c‖ ^ 2 * (φ.value (leftSquare (x : A))).toReal
  exact hvalue.trans (φ.toReal_positiveSmul (NNReal.mk (‖c‖ ^ 2) (sq_nonneg ‖c‖)) (leftSquare (x : A)))

/-- **Real polarization at a zero first argument.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. For `x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i • x,y)`.
`R(0,y)=0` for every `y ∈ n_φ`. -/
theorem Weight.finiteSquarePolarRe_zero (φ : Weight A) (y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe 0 y = 0 := by
  simp only [Weight.finiteSquarePolarRe, zero_add, zero_sub, φ.finiteSquareValue_neg,
    sub_self, zero_div]

/-- **Additivity of real weight polarization.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. For `x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i • x,y)`.
`R(x+y,z)=R(x,z)+R(y,z)` for `x,y,z ∈ n_φ`. -/
theorem Weight.finiteSquarePolarRe_add (φ : Weight A) (x y z : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe (x + y) z = φ.finiteSquarePolarRe x z + φ.finiteSquarePolarRe y z := by
  have hraw :
      (leftSquare (((x + y) + z : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare (((x + y) - z : φ.finiteSquareSubmodule) : A) : A) =
      ((leftSquare ((x + z : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare ((x - z : φ.finiteSquareSubmodule) : A) : A)) +
      ((leftSquare ((y + z : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare ((y - z : φ.finiteSquareSubmodule) : A) : A)) := by
    change (leftSquare ((x : A) + (y : A) + (z : A)) : A) -
      (leftSquare ((x : A) + (y : A) - (z : A)) : A) =
      ((leftSquare ((x : A) + (z : A)) : A) - (leftSquare ((x : A) - (z : A)) : A)) +
      ((leftSquare ((y : A) + (z : A)) : A) - (leftSquare ((y : A) - (z : A)) : A))
    simp only [leftSquare_difference, star_add, add_mul, mul_add]
    abel
  have h := φ.finite_toReal_sub_eq_add_sub
    (leftSquare (((x + y) + z : φ.finiteSquareSubmodule) : A))
    (leftSquare (((x + y) - z : φ.finiteSquareSubmodule) : A))
    (leftSquare ((x + z : φ.finiteSquareSubmodule) : A))
    (leftSquare ((x - z : φ.finiteSquareSubmodule) : A))
    (leftSquare ((y + z : φ.finiteSquareSubmodule) : A))
    (leftSquare ((y - z : φ.finiteSquareSubmodule) : A))
    (x + y + z).property (x + y - z).property (x + z).property (x - z).property
    (y + z).property (y - z).property hraw
  dsimp only [Weight.finiteSquarePolarRe, Weight.finiteSquareValue]
  linarith [h]

/-- **Negation in real weight polarization.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. For `x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i • x,y)`.
`R(-x,y)=-R(x,y)` for `x,y ∈ n_φ`. -/
theorem Weight.finiteSquarePolarRe_neg (φ : Weight A) (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe (-x) y = -φ.finiteSquarePolarRe x y := by
  have h := φ.finiteSquarePolarRe_add x (-x) y
  rw [add_neg_cancel, φ.finiteSquarePolarRe_zero] at h
  linarith

/-- **Symmetry of real weight polarization.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. For `x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i • x,y)`.
`R(x,y)=R(y,x)` for `x,y ∈ n_φ`. -/
theorem Weight.finiteSquarePolarRe_symm (φ : Weight A) (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe x y = φ.finiteSquarePolarRe y x := by
  have hraw :
      (leftSquare ((x + y : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare ((x - y : φ.finiteSquareSubmodule) : A) : A) =
      (leftSquare ((y + x : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare ((y - x : φ.finiteSquareSubmodule) : A) : A) := by
    change (leftSquare ((x : A) + (y : A)) : A) - (leftSquare ((x : A) - (y : A)) : A) =
      (leftSquare ((y : A) + (x : A)) : A) - (leftSquare ((y : A) - (x : A)) : A)
    simp only [leftSquare_difference]
    abel
  have h := φ.finite_toReal_sub_eq_sub
    (leftSquare ((x + y : φ.finiteSquareSubmodule) : A))
    (leftSquare ((x - y : φ.finiteSquareSubmodule) : A))
    (leftSquare ((y + x : φ.finiteSquareSubmodule) : A))
    (leftSquare ((y - x : φ.finiteSquareSubmodule) : A))
    (x + y).property (x - y).property (y + x).property (y - x).property hraw
  dsimp only [Weight.finiteSquarePolarRe, Weight.finiteSquareValue]
  linarith [h]

/-- **Real scaling in weight polarization.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. For `x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i • x,y)`. for
any `r : ℝ`, viewed as a complex scalar, `R(r • x,y)=r R(x,y)` for `x,y ∈ n_φ`. -/
theorem Weight.finiteSquarePolarRe_smul_real (φ : Weight A) (r : ℝ)
    (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe ((RCLike.ofReal r : ℂ) • x) y = r * φ.finiteSquarePolarRe x y := by
  have hscalar : (RCLike.ofReal r : ℂ) • (x : A) = r • (x : A) :=
    (RCLike.real_smul_eq_coe_smul (K := ℂ) r (x : A)).symm
  have hraw :
      (leftSquare ((((RCLike.ofReal r : ℂ) • x) + y : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare ((((RCLike.ofReal r : ℂ) • x) - y : φ.finiteSquareSubmodule) : A) : A) =
      r • ((leftSquare ((x + y : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare ((x - y : φ.finiteSquareSubmodule) : A) : A)) := by
    change (leftSquare ((RCLike.ofReal r : ℂ) • (x : A) + (y : A)) : A) -
      (leftSquare ((RCLike.ofReal r : ℂ) • (x : A) - (y : A)) : A) =
      r • ((leftSquare ((x : A) + (y : A)) : A) - (leftSquare ((x : A) - (y : A)) : A))
    rw [hscalar]
    simp only [leftSquare_difference, star_smul, star_trivial, smul_mul_assoc,
      mul_smul_comm, smul_add]
  have h := φ.finite_toReal_sub_eq_real_smul_sub r
    (leftSquare ((((RCLike.ofReal r : ℂ) • x) + y : φ.finiteSquareSubmodule) : A))
    (leftSquare ((((RCLike.ofReal r : ℂ) • x) - y : φ.finiteSquareSubmodule) : A))
    (leftSquare ((x + y : φ.finiteSquareSubmodule) : A))
    (leftSquare ((x - y : φ.finiteSquareSubmodule) : A))
    (((RCLike.ofReal r : ℂ) • x) + y).property (((RCLike.ofReal r : ℂ) • x) - y).property
    (x + y).property (x - y).property hraw
  dsimp only [Weight.finiteSquarePolarRe, Weight.finiteSquareValue]
  linarith [h]

/-- **Skew symmetry of the imaginary polarization.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. For `x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i • x,y)`. `R(i
• x,y)=-R(i • y,x)` for `x,y ∈ n_φ`. -/
theorem Weight.finiteSquarePolarRe_I_antisymm (φ : Weight A) (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe (Complex.I • x) y = -φ.finiteSquarePolarRe (Complex.I • y) x := by
  have hraw :
      (leftSquare (((Complex.I • x) + y : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare (((Complex.I • x) - y : φ.finiteSquareSubmodule) : A) : A) =
      (leftSquare (((Complex.I • y) - x : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare (((Complex.I • y) + x : φ.finiteSquareSubmodule) : A) : A) := by
    change (leftSquare (Complex.I • (x : A) + (y : A)) : A) -
      (leftSquare (Complex.I • (x : A) - (y : A)) : A) =
      (leftSquare (Complex.I • (y : A) - (x : A)) : A) -
      (leftSquare (Complex.I • (y : A) + (x : A)) : A)
    have hreverse :
        (leftSquare (Complex.I • (y : A) - (x : A)) : A) -
          (leftSquare (Complex.I • (y : A) + (x : A)) : A) =
        -((leftSquare (Complex.I • (y : A) + (x : A)) : A) -
          (leftSquare (Complex.I • (y : A) - (x : A)) : A)) := by abel
    rw [hreverse]
    simp only [leftSquare_difference, star_smul, Complex.star_def, Complex.conj_I,
      neg_smul, neg_mul, smul_mul_assoc, mul_smul_comm]
    abel
  have h := φ.finite_toReal_sub_eq_sub
    (leftSquare (((Complex.I • x) + y : φ.finiteSquareSubmodule) : A))
    (leftSquare (((Complex.I • x) - y : φ.finiteSquareSubmodule) : A))
    (leftSquare (((Complex.I • y) - x : φ.finiteSquareSubmodule) : A))
    (leftSquare (((Complex.I • y) + x : φ.finiteSquareSubmodule) : A))
    ((Complex.I • x) + y).property ((Complex.I • x) - y).property
    ((Complex.I • y) - x).property ((Complex.I • y) + x).property hraw
  dsimp only [Weight.finiteSquarePolarRe, Weight.finiteSquareValue]
  linarith [h]

/-- **Hermitian symmetry of the polarized weight.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. For `x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i • x,y)`.
`conj(P(y,x))=P(x,y)` for `x,y ∈ n_φ`. -/
theorem Weight.finiteSquarePolarInner_conj_symm (φ : Weight A) (x y : φ.finiteSquareSubmodule) :
    (starRingEnd ℂ) (φ.finiteSquarePolarInner y x) = φ.finiteSquarePolarInner x y := by
  apply Complex.ext
  · rw [Complex.conj_re]
    change φ.finiteSquarePolarRe y x = φ.finiteSquarePolarRe x y
    exact φ.finiteSquarePolarRe_symm y x
  · rw [Complex.conj_im]
    change -φ.finiteSquarePolarRe (Complex.I • y) x = φ.finiteSquarePolarRe (Complex.I • x) y
    have h := φ.finiteSquarePolarRe_I_antisymm y x
    linarith

/-- **Additivity of the complex weight form.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. For `x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i • x,y)`.
`P(x+y,z)=P(x,z)+P(y,z)` for `x,y,z ∈ n_φ`. -/
theorem Weight.finiteSquarePolarInner_add (φ : Weight A) (x y z : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarInner (x + y) z = φ.finiteSquarePolarInner x z + φ.finiteSquarePolarInner y z := by
  apply Complex.ext
  · rw [Complex.add_re]
    change φ.finiteSquarePolarRe (x + y) z = φ.finiteSquarePolarRe x z + φ.finiteSquarePolarRe y z
    exact φ.finiteSquarePolarRe_add x y z
  · rw [Complex.add_im]
    change φ.finiteSquarePolarRe (Complex.I • (x + y)) z =
      φ.finiteSquarePolarRe (Complex.I • x) z + φ.finiteSquarePolarRe (Complex.I • y) z
    rw [smul_add]
    exact φ.finiteSquarePolarRe_add (Complex.I • x) (Complex.I • y) z

/-- **Real scaling of the complex weight form.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. For `x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i • x,y)`. for
any `r : ℝ` viewed as a complex scalar, `P(r • x,y)=r P(x,y)` for `x,y ∈ n_φ`. -/
theorem Weight.finiteSquarePolarInner_smul_real (φ : Weight A) (r : ℝ)
    (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarInner ((RCLike.ofReal r : ℂ) • x) y =
      (RCLike.ofReal r : ℂ) * φ.finiteSquarePolarInner x y := by
  have hcomm : Complex.I • ((RCLike.ofReal r : ℂ) • x) =
      (RCLike.ofReal r : ℂ) • (Complex.I • x) := smul_comm Complex.I (RCLike.ofReal r : ℂ) x
  have hre : (RCLike.ofReal r : ℂ).re = r := by
    simpa only [RCLike.re_to_complex] using (RCLike.ofReal_re (K := ℂ) r)
  have him : (RCLike.ofReal r : ℂ).im = 0 := by
    simpa only [RCLike.im_to_complex] using (RCLike.ofReal_im (K := ℂ) r)
  apply Complex.ext
  · rw [Complex.mul_re, hre, him]
    change φ.finiteSquarePolarRe ((RCLike.ofReal r : ℂ) • x) y =
      r * φ.finiteSquarePolarRe x y - 0 * φ.finiteSquarePolarRe (Complex.I • x) y
    rw [zero_mul, sub_zero]
    exact φ.finiteSquarePolarRe_smul_real r x y
  · rw [Complex.mul_im, hre, him]
    change φ.finiteSquarePolarRe (Complex.I • ((RCLike.ofReal r : ℂ) • x)) y =
      r * φ.finiteSquarePolarRe (Complex.I • x) y + 0 * φ.finiteSquarePolarRe x y
    rw [hcomm, zero_mul, add_zero]
    exact φ.finiteSquarePolarRe_smul_real r (Complex.I • x) y

/-- **Conjugate-linear imaginary scaling.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. For
`x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i • x,y)`. `P(i • x,y)=-i
P(x,y)` for `x,y ∈ n_φ`. -/
theorem Weight.finiteSquarePolarInner_smul_I (φ : Weight A) (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarInner (Complex.I • x) y = -Complex.I * φ.finiteSquarePolarInner x y := by
  have hII : Complex.I • (Complex.I • x) = -x := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  apply Complex.ext
  · rw [Complex.mul_re]
    change φ.finiteSquarePolarRe (Complex.I • x) y =
      (-Complex.I).re * φ.finiteSquarePolarRe x y -
        (-Complex.I).im * φ.finiteSquarePolarRe (Complex.I • x) y
    simp only [Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    ring
  · rw [Complex.mul_im]
    change φ.finiteSquarePolarRe (Complex.I • (Complex.I • x)) y =
      (-Complex.I).re * φ.finiteSquarePolarRe (Complex.I • x) y +
        (-Complex.I).im * φ.finiteSquarePolarRe x y
    rw [hII, φ.finiteSquarePolarRe_neg]
    simp only [Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    ring

/-- **Conjugate linearity of weight polarization.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. For `x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i • x,y)`. for
every `c : ℂ`, `P(c • x,y)=conj(c) P(x,y)` for `x,y ∈ n_φ`. -/
theorem Weight.finiteSquarePolarInner_smul (φ : Weight A) (c : ℂ) (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarInner (c • x) y = (starRingEnd ℂ) c * φ.finiteSquarePolarInner x y := by
  let r : ℝ := RCLike.re c
  let s : ℝ := RCLike.im c
  have hc : c = (RCLike.ofReal r : ℂ) + (RCLike.ofReal s : ℂ) * Complex.I :=
    (RCLike.re_add_im c).symm
  rw [hc, add_smul, φ.finiteSquarePolarInner_add,
    ← smul_smul (RCLike.ofReal s : ℂ) Complex.I x,
    φ.finiteSquarePolarInner_smul_real r, φ.finiteSquarePolarInner_smul_real s,
    φ.finiteSquarePolarInner_smul_I]
  simp only [map_add, map_mul, RCLike.conj_ofReal, Complex.conj_I]
  ring

/-- **Real diagonal of the weight polarization.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. For `x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i • x,y)`.
`R(x,x)=q(x)` for every `x ∈ n_φ`. -/
theorem Weight.finiteSquarePolarRe_self (φ : Weight A) (x : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe x x = φ.finiteSquareValue x := by
  have htwo : x + x = (2 : ℂ) • x := (two_smul ℂ x).symm
  simp only [Weight.finiteSquarePolarRe, htwo, sub_self, φ.finiteSquareValue_zero,
    φ.finiteSquareValue_smul]
  norm_num

/-- **Positive diagonal of the complex weight form.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. For `x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i •
x,y)`. `P(x,x)=(q(x) : ℂ)` for every `x ∈ n_φ`, so the diagonal is real and nonnegative. -/
theorem Weight.finiteSquarePolarInner_self (φ : Weight A) (x : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarInner x x = (RCLike.ofReal (φ.finiteSquareValue x) : ℂ) := by
  have him := φ.finiteSquarePolarRe_I_antisymm x x
  have hre : (RCLike.ofReal (φ.finiteSquareValue x) : ℂ).re = φ.finiteSquareValue x := by
    simpa only [RCLike.re_to_complex] using (RCLike.ofReal_re (K := ℂ) (φ.finiteSquareValue x))
  have himzero : (RCLike.ofReal (φ.finiteSquareValue x) : ℂ).im = 0 := by
    simpa only [RCLike.im_to_complex] using (RCLike.ofReal_im (K := ℂ) (φ.finiteSquareValue x))
  apply Complex.ext
  · change φ.finiteSquarePolarRe x x = (RCLike.ofReal (φ.finiteSquareValue x) : ℂ).re
    rw [φ.finiteSquarePolarRe_self, hre]
  · change φ.finiteSquarePolarRe (Complex.I • x) x =
      (RCLike.ofReal (φ.finiteSquareValue x) : ℂ).im
    rw [himzero]
    linarith

/-- **Type copy of the finite square module.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. `PreGNS φ` is a type copy of the
complex submodule `n_φ`, on which the weight pairing and seminorm can be installed separately
from the ambient norm of `A`. -/
def Weight.PreGNS (φ : Weight A) : Type u := φ.finiteSquareSubmodule

/-- **Addition on the pre-GNS domain.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. the type copy `PreGNS φ` has zero, addition and
negation inherited from the finite square complex module `n_φ`. -/
instance Weight.preGNSAddCommGroup (φ : Weight A) : AddCommGroup φ.PreGNS :=
  inferInstanceAs (AddCommGroup φ.finiteSquareSubmodule)

/-- **Complex scalars on the pre-GNS domain.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. the type copy `PreGNS φ` has the
complex scalar action inherited from `n_φ`, sending `x` to `c • x` in `A`. -/
instance Weight.preGNSModule (φ : Weight A) : Module ℂ φ.PreGNS :=
  inferInstanceAs (Module ℂ φ.finiteSquareSubmodule)

/-- **Linear identification of the pre-GNS type copy.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. `preGNSLinearEquiv φ : PreGNS φ
≃ₗ[ℂ] n_φ` is the identity on algebra elements in both directions. -/
def Weight.preGNSLinearEquiv (φ : Weight A) : φ.PreGNS ≃ₗ[ℂ] φ.finiteSquareSubmodule where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Positive semidefinite pre-GNS core.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. For
`x,y ∈ n_φ`, write `R(x,y)=(q(x+y)-q(x-y))/4` and `P(x,y)=R(x,y)+i R(i • x,y)`. for
`e=preGNSLinearEquiv φ`, the core on `PreGNS φ` has `inner x y=P(e(x),e(y))`, Hermitian
symmetry, nonnegative real diagonal, additivity and conjugate linearity in the first argument. -/
@[instance_reducible]
def Weight.preGNSPreInnerProduct (φ : Weight A) : PreInnerProductSpace.Core ℂ φ.PreGNS where
  inner x y := φ.finiteSquarePolarInner (φ.preGNSLinearEquiv x) (φ.preGNSLinearEquiv y)
  conj_inner_symm x y := φ.finiteSquarePolarInner_conj_symm _ _
  re_inner_nonneg x := by
    rw [φ.finiteSquarePolarInner_self, RCLike.ofReal_re]
    exact φ.finiteSquareValue_nonneg _
  add_left x y z := by
    rw [map_add]
    exact φ.finiteSquarePolarInner_add _ _ _
  smul_left x y c := by
    change φ.finiteSquarePolarInner (φ.preGNSLinearEquiv (c • x)) (φ.preGNSLinearEquiv y) = _
    rw [map_smul]
    exact φ.finiteSquarePolarInner_smul _ _ _

end

end CStarAlgebra.ScalarWeight
