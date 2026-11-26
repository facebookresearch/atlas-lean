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

public import MathlibExt.Analysis.CStarAlgebra.Weight
public import Mathlib.Algebra.Group.Action.Units

/-!
# Nonnegative scalar action on positive weights

For a nonunital complex C-star algebra `A`, finite nonnegative real scalars act on extended
positive weights by `(r • φ)(a)=r φ(a)` for `a ≥ 0`. The product is in `[0,∞]`, including its
convention `0*∞=0`.

The identities `1 • φ=φ` and `(r*t) • φ=r • (t • φ)` give a multiplicative monoid action of
`ℝ≥0`. Its unit group, the strictly positive finite real scalars, acts by the same formula. No
faithfulness, trace or normality condition is imposed on the weights.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **Scaled extended positive weight.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. for finite `r : ℝ≥0`, `scale r φ` is the weight `a ↦ r φ(a)` on the positive cone;
when `r=0` it is zero even at infinite weight values. -/
def Weight.scale (r : NNReal) (φ : Weight A) : Weight A where
  value a := (r : ENNReal) * φ.value a
  zero_value := by
    rw [φ.zero_value, mul_zero]
  add_value a b := by
    rw [φ.add_value, mul_add]
  smul_value t a := by
    rw [φ.smul_value]
    exact mul_left_comm (r : ENNReal) (t : ENNReal) (φ.value a)

/-- **Positive value of a scaled weight.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. for `r : ℝ≥0` and positive `a : A`, `(scale r φ)(a)=(r : [0,∞])*φ(a)`. -/
@[simp]
theorem Weight.scale_value (r : NNReal) (φ : Weight A) (a : PositiveElement A) :
    (Weight.scale r φ).value a = (r : ENNReal) * φ.value a :=
  rfl

/-- **Identity scalar fixes a positive weight.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. `scale 1 φ=φ`. -/
theorem Weight.scale_one (φ : Weight A) : Weight.scale 1 φ = φ := by
  apply Weight.ext_value
  intro a
  rw [Weight.scale_value, ENNReal.coe_one, one_mul]

/-- **Composition of weight scalings.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. for finite `r,t : ℝ≥0`, `scale (r*t) φ=scale r (scale t φ)`. -/
theorem Weight.scale_mul (r t : NNReal) (φ : Weight A) :
    Weight.scale (r * t) φ = Weight.scale r (Weight.scale t φ) := by
  apply Weight.ext_value
  intro a
  rw [Weight.scale_value, Weight.scale_value, Weight.scale_value, ENNReal.coe_mul, mul_assoc]

/-- **Nonnegative scalar monoid action on weights.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. finite nonnegative real scalars act on `Weight A` by `(r • φ)(a)=r φ(a)`,
with `1 • φ=φ` and `(r*t) • φ=r • (t • φ)`. -/
instance instMulActionWeight : MulAction NNReal (Weight A) where
  smul := Weight.scale
  one_smul := Weight.scale_one
  mul_smul := Weight.scale_mul

/-- **Positive scalar unit action on weights.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. for a unit `r : ℝ≥0ˣ`, hence a strictly positive finite real scalar, `(r •
φ)(a)=r φ(a)` for every positive `a : A`. -/
theorem Weight.units_smul_value (r : NNRealˣ) (φ : Weight A) (a : PositiveElement A) :
    (r • φ).value a = ((r : NNReal) : ENNReal) * φ.value a :=
  rfl

end

end CStarAlgebra.ScalarWeight
