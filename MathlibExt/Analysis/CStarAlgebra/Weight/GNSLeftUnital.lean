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

public import MathlibExt.Analysis.CStarAlgebra.Weight.GNSLeftRepresentation
public import Mathlib.Algebra.Algebra.Hom

/-!
# The original unital weight algebra has its actual unital GNS star map

The completed original left operator at one fixes the canonical dense
GNS map, because original left multiplication by one fixes each actual
finite-square element. This proves the identity operator law and turns
the existing nonunital star representation into a unital star algebra map.

The map is the same original completed left action. Unitality, a norm
certificate or a normal/faithful representation is not supplied as input.
The original zero algebra is allowed. Normality, faithful range, full
finite integration extension and Tomita/modular/polar data remain separate.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- Original multiplication by one gives the identity on the actual weight completion. -/
theorem Weight.gnsLeftMul_one (φ : Weight A) : φ.gnsLeftMul (1 : A) = 1 := by
  ext z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
      change φ.gnsLeftMul 1 (φ.toGNS x) = φ.toGNS x
      rw [φ.gnsLeftMul_toGNS]
      apply congrArg φ.toGNS
      apply φ.preGNSLinearEquiv.injective
      apply Subtype.ext
      rw [φ.preGNSLeftMul_originalValue]
      exact one_mul _

/-- The actual unital star map packages the same original nonunital weight representation. -/
def Weight.gnsLeftStarAlgHom (φ : Weight A) : A →⋆ₐ[ℂ] (φ.GNS →L[ℂ] φ.GNS) where
  toAlgHom := AlgHom.mk'
    { toFun := φ.gnsLeftRepresentation
      map_zero' := map_zero φ.gnsLeftRepresentation
      map_one' := by
        change φ.gnsLeftMul (1 : A) = 1
        exact φ.gnsLeftMul_one
      map_add' a b := map_add φ.gnsLeftRepresentation a b
      map_mul' a b := map_mul φ.gnsLeftRepresentation a b }
    (fun c a => map_smul φ.gnsLeftRepresentation c a)
  map_star' a := map_star φ.gnsLeftRepresentation a

/-- The unital map retains exactly the existing original completed coefficient operator. -/
theorem Weight.gnsLeftStarAlgHom_apply (φ : Weight A) (a : A) :
    φ.gnsLeftStarAlgHom a = φ.gnsLeftRepresentation a :=
  rfl

/-- The unital map has the same original finite-square dense-domain multiplication values. -/
theorem Weight.gnsLeftStarAlgHom_gnsMap (φ : Weight A) (a : A) (x : φ.finiteSquareSubmodule) :
    φ.gnsLeftStarAlgHom a (φ.gnsMap x) = φ.gnsMap (φ.finiteSquareLeftMul a x) :=
  φ.gnsLeftRepresentation_gnsMap a x

end

end CStarAlgebra.ScalarWeight
