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

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.Coalgebra

/-!
# The actual reduced primitive equation for the exterior coalgebra

The counit condition follows from the primitive coproduct equation by
counitality and additive cancellation. No division by two and no
characteristic hypothesis is needed. This is the actual primitive equation
for the constructed exterior coproduct and its actual multiplicative unit.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

local notation "E" => ExteriorAlgebra R M

/-- The actual reduced primitive map on the exterior algebra. -/
def primitiveEquation : E →ₗ[R] E ⊗[R] E :=
  coproduct R M - ((TensorProduct.mk R E E).flip (1 : E) + TensorProduct.mk R E E (1 : E))

@[simp]
theorem primitiveEquation_apply (a : E) :
    primitiveEquation R M a = coproduct R M a - (a ⊗ₜ[R] (1 : E) + (1 : E) ⊗ₜ[R] a) := rfl

/-- The actual reduced equation is equivalent to native primitivity over every commutative ring. -/
theorem primitiveEquation_eq_zero_iff (a : E) :
    primitiveEquation R M a = 0 ↔ Coalgebra.IsSkewPrimitiveElem R (1 : E) (1 : E) a := by
  constructor
  · intro h
    rw [primitiveEquation_apply] at h
    have hΔ : Coalgebra.comul a = (1 : E) ⊗ₜ[R] a + a ⊗ₜ[R] (1 : E) := by
      change coproduct R M a = _
      simpa only [add_comm] using sub_eq_zero.mp h
    apply Coalgebra.IsSkewPrimitiveElem.of_comul_eq_tmul_add_tmul
    · change augmentation R M (1 : E) = 1
      exact map_one (augmentation R M)
    · change augmentation R M (1 : E) = 1
      exact map_one (augmentation R M)
    · exact hΔ
  · intro h
    rw [primitiveEquation_apply]
    change Coalgebra.comul a - (a ⊗ₜ[R] (1 : E) + (1 : E) ⊗ₜ[R] a) = 0
    rw [h.comul_eq_tmul_add_tmul, add_comm, sub_self]

end ExteriorAlgebra
