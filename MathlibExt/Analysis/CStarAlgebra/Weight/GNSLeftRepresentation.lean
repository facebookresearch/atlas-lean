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
# The actual nonunital star representation of the original weight algebra

The actual completed left operators preserve zero, addition, complex
scalars and multiplication by their original canonical dense-domain values.
Together with the proved original adjoint law, these construct the literal
nonunital star algebra homomorphism into the bounded operators on the
actual weight Hilbert completion.

No normal/faithful representation or Hilbert/norm certificate is supplied.
Only the original possibly nonunital C-star algebra and its global positive
weight occur as input. Representation faithfulness/normality/range, the full
finite integration extension and Tomita/modular/polar constructions remain
separate; no original source theorem supplies chosen DATA.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The actual completed original left representation sends the zero coefficient to zero. -/
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

/-- Addition of original coefficients is addition of the actual completed left operators. -/
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

/-- Original complex coefficient scaling scales the actual completed left operator. -/
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

/-- Multiplication of original coefficients is composition of the actual completed left operators. -/
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

/-- The original global-weight left action as its actual nonunital star representation. -/
def Weight.gnsLeftRepresentation (φ : Weight A) : A →⋆ₙₐ[ℂ] (φ.GNS →L[ℂ] φ.GNS) where
  toFun := φ.gnsLeftMul
  map_zero' := φ.gnsLeftMul_zero
  map_add' a b := φ.gnsLeftMul_add a b
  map_smul' c a := φ.gnsLeftMul_smul c a
  map_mul' a b := φ.gnsLeftMul_mul a b
  map_star' a := φ.gnsLeftMul_star a

/-- The actual star representation retains every original completed left operator. -/
theorem Weight.gnsLeftRepresentation_apply (φ : Weight A) (a : A) :
    φ.gnsLeftRepresentation a = φ.gnsLeftMul a :=
  rfl

/-- The actual representation has the literal original finite-square multiplication values. -/
theorem Weight.gnsLeftRepresentation_gnsMap (φ : Weight A) (a : A) (x : φ.finiteSquareSubmodule) :
    φ.gnsLeftRepresentation a (φ.gnsMap x) = φ.gnsMap (φ.finiteSquareLeftMul a x) :=
  φ.gnsLeftMul_gnsMap a x

end

end CStarAlgebra.ScalarWeight
