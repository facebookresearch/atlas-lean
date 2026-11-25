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

public import MathlibExt.Analysis.CStarAlgebra.Weight.GNSLeftAdjoint

/-!
# Star representation by GNS left multiplication

For an extended positive weight `φ` on a nonunital complex C-star algebra `A`, completed left
multiplication gives a nonunital complex star homomorphism `π : A → B(H_φ)` satisfying
`π(a)Λ(x)=Λ(a*x)`.

It preserves zero, addition, complex scalars and multiplication, and `π(a*)=π(a)*`. The
construction permits degenerate weights and zero GNS spaces; it does not require faithfulness,
normality or density of the finite square domain in `A`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **Zero coefficient in the GNS left action.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. `gnsLeftMul φ (0 : A)=0` as a bounded operator on `H_φ`. -/
theorem Weight.gnsLeftMul_zero (φ : Weight A) : φ.gnsLeftMul (0 : A) = 0 := by
  ext z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
      change φ.gnsLeftMul 0 (φ.toGNS x) = 0
      rw [φ.gnsLeftMul_toGNS]
      have hzero : φ.preGNSLeftMul 0 x = 0 := by
        apply φ.preGNSLinearEquiv.injective
        rw [map_zero]
        apply Subtype.ext
        rw [φ.preGNSLeftMul_originalValue]
        exact zero_mul _
      rw [hzero, map_zero]

/-- **Additivity of completed GNS left multiplication.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. `gnsLeftMul φ (a+b)=gnsLeftMul φ a+gnsLeftMul φ b` for
`a,b : A`. -/
theorem Weight.gnsLeftMul_add (φ : Weight A) (a b : A) :
    φ.gnsLeftMul (a + b) = φ.gnsLeftMul a + φ.gnsLeftMul b := by
  ext z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
      change φ.gnsLeftMul (a + b) (φ.toGNS x) =
        φ.gnsLeftMul a (φ.toGNS x) + φ.gnsLeftMul b (φ.toGNS x)
      rw [φ.gnsLeftMul_toGNS, φ.gnsLeftMul_toGNS, φ.gnsLeftMul_toGNS, ← map_add]
      apply congrArg φ.toGNS
      apply φ.preGNSLinearEquiv.injective
      rw [map_add]
      apply Subtype.ext
      change (φ.preGNSLinearEquiv (φ.preGNSLeftMul (a + b) x) : A) =
        (φ.preGNSLinearEquiv (φ.preGNSLeftMul a x) : A) +
          (φ.preGNSLinearEquiv (φ.preGNSLeftMul b x) : A)
      rw [φ.preGNSLeftMul_originalValue, φ.preGNSLeftMul_originalValue,
        φ.preGNSLeftMul_originalValue]
      exact add_mul a b _

/-- **Complex linearity of the completed GNS action.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. for `c : ℂ` and `a : A`, `gnsLeftMul φ (c • a)=c •
gnsLeftMul φ a`. -/
theorem Weight.gnsLeftMul_smul (φ : Weight A) (c : ℂ) (a : A) :
    φ.gnsLeftMul (c • a) = c • φ.gnsLeftMul a := by
  ext z
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      change IsClosed {z : φ.GNS | φ.gnsLeftMul (c • a) z = c • φ.gnsLeftMul a z}
      have hscalar : Continuous (fun z : φ.GNS => c • φ.gnsLeftMul a z) :=
        (φ.gnsLeftMul a).continuous.const_smul c
      exact isClosed_eq (φ.gnsLeftMul (c • a)).continuous hscalar
  | ih x =>
      change φ.gnsLeftMul (c • a) (φ.toGNS x) = c • φ.gnsLeftMul a (φ.toGNS x)
      have hpre : φ.preGNSLeftMul (c • a) x = c • φ.preGNSLeftMul a x := by
        apply φ.preGNSLinearEquiv.injective
        rw [φ.preGNSLinearEquiv.map_smul c (φ.preGNSLeftMul a x)]
        apply Subtype.ext
        change (φ.preGNSLinearEquiv (φ.preGNSLeftMul (c • a) x) : A) =
          c • (φ.preGNSLinearEquiv (φ.preGNSLeftMul a x) : A)
        rw [φ.preGNSLeftMul_originalValue, φ.preGNSLeftMul_originalValue]
        exact smul_mul_assoc c a _
      calc
        φ.gnsLeftMul (c • a) (φ.toGNS x) = φ.toGNS (φ.preGNSLeftMul (c • a) x) :=
          φ.gnsLeftMul_toGNS (c • a) x
        _ = φ.toGNS (c • φ.preGNSLeftMul a x) := congrArg φ.toGNS hpre
        _ = c • φ.toGNS (φ.preGNSLeftMul a x) := φ.toGNS.map_smul c (φ.preGNSLeftMul a x)
        _ = c • φ.gnsLeftMul a (φ.toGNS x) :=
          congrArg (fun y : φ.GNS => c • y) (φ.gnsLeftMul_toGNS a x).symm

/-- **Multiplication in the GNS left representation.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. for `a,b : A`, `gnsLeftMul φ (a*b)=gnsLeftMul φ a *
gnsLeftMul φ b`, where operator multiplication is composition. -/
theorem Weight.gnsLeftMul_mul (φ : Weight A) (a b : A) :
    φ.gnsLeftMul (a * b) = φ.gnsLeftMul a * φ.gnsLeftMul b := by
  ext z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
      change φ.gnsLeftMul (a * b) (φ.toGNS x) =
        φ.gnsLeftMul a (φ.gnsLeftMul b (φ.toGNS x))
      rw [φ.gnsLeftMul_toGNS, φ.gnsLeftMul_toGNS, φ.gnsLeftMul_toGNS]
      apply congrArg φ.toGNS
      apply φ.preGNSLinearEquiv.injective
      apply Subtype.ext
      rw [φ.preGNSLeftMul_originalValue, φ.preGNSLeftMul_originalValue,
        φ.preGNSLeftMul_originalValue]
      exact mul_assoc a b _

/-- **Nonunital star representation of a positive weight.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. `gnsLeftRepresentation φ : A →⋆ₙₐ[ℂ] B(H_φ)` sends `a` to
the completion of left multiplication and satisfies `π(a)Λ(x)=Λ(a*x)`. -/
def Weight.gnsLeftRepresentation (φ : Weight A) : A →⋆ₙₐ[ℂ] (φ.GNS →L[ℂ] φ.GNS) where
  toFun := φ.gnsLeftMul
  map_zero' := φ.gnsLeftMul_zero
  map_add' a b := φ.gnsLeftMul_add a b
  map_smul' c a := φ.gnsLeftMul_smul c a
  map_mul' a b := φ.gnsLeftMul_mul a b
  map_star' a := φ.gnsLeftMul_star a

/-- **Operator value of the GNS star representation.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. for `a : A`, `gnsLeftRepresentation φ a = gnsLeftMul φ a`,
the bounded completed left operator. -/
theorem Weight.gnsLeftRepresentation_apply (φ : Weight A) (a : A) :
    φ.gnsLeftRepresentation a = φ.gnsLeftMul a :=
  rfl

/-- **GNS representation on its dense square domain.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. for `a : A` and `x ∈ n_φ`, `gnsLeftRepresentation φ a (Λ
x)=Λ(a*x)`. -/
theorem Weight.gnsLeftRepresentation_gnsMap (φ : Weight A) (a : A) (x : φ.finiteSquareSubmodule) :
    φ.gnsLeftRepresentation a (φ.gnsMap x) = φ.gnsMap (φ.finiteSquareLeftMul a x) :=
  φ.gnsLeftMul_gnsMap a x

end

end CStarAlgebra.ScalarWeight
