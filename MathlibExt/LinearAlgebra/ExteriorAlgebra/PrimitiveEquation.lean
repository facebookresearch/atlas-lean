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
# The reduced exterior primitive equation

For an R-module M over a commutative ring R, define the R-linear map ∆̄ : ExteriorAlgebra R M
→ ExteriorAlgebra R M ⊗_R ExteriorAlgebra R M by ∆̄(a)=∆(a)−a⊗1−1⊗a.

Its zero set is exactly the set of primitive elements. The zero-counit condition follows from
the coproduct equation by counitality and additive cancellation, so no characteristic or
invertibility-of-two hypothesis is needed.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

local notation "E" => ExteriorAlgebra R M

/-- Let R be a commutative ring and M an R-module. For E=ExteriorAlgebra R M, define the R-linear
map E → E⊗_R E by a ↦ ∆(a)−a⊗1−1⊗a, using the exterior coproduct and its unit. This map
vanishes precisely when the coproduct has the primitive form. -/
def primitiveEquation : E →ₗ[R] E ⊗[R] E :=
  coproduct R M - ((TensorProduct.mk R E E).flip (1 : E) + TensorProduct.mk R E E (1 : E))

@[simp]
theorem primitiveEquation_apply (a : E) :
    primitiveEquation R M a = coproduct R M a - (a ⊗ₜ[R] (1 : E) + (1 : E) ⊗ₜ[R] a) := rfl

/-- For an R-module M over a commutative ring R and a ∈ ExteriorAlgebra R M, ∆(a)−a⊗1−1⊗a=0 if and
only if a is (1,1)-skew primitive. The coproduct equation implies the zero-counit condition by
counitality and additive cancellation. Thus the equivalence holds over every commutative ring,
without a characteristic assumption. -/
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
