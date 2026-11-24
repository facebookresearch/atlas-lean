/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Ring.K1.DeterminantScalarMap

/-! # Original determinant clients in independent coefficient universes -/

@[expose] public section

noncomputable section

set_option autoImplicit false

open AlgebraicKTheory

universe uR uS uT

namespace MathlibExtTest.KTheory.Ring.K1.DeterminantScalarMapTests

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [CommRing R] [CommRing S] [CommRing T]

/-- Three actual ring worlds retain the composed original determinant square. -/
theorem three_world_determinant (φ : R →+* S) (ψ : S →+* T) (a : K1 R) :
    K1.detHom (R := T) (K1.mapRingHom ψ (K1.mapRingHom φ a)) =
      (Units.map ψ.toMonoidHom).toAdditive
        ((Units.map φ.toMonoidHom).toAdditive (K1.detHom (R := R) a)) := by
  rw [K1.detHom_mapRingHom, K1.detHom_mapRingHom]

/-- Original finite matrix representatives compute the same coefficient-mapped determinant units. -/
theorem mapped_matrix_determinant (φ : R →+* S) {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) R) :
    K1.detHom (R := S) (K1.mapRingHom φ (K1.mk A)) =
      Additive.ofMul ((Matrix.GeneralLinearGroup.det A).map φ.toMonoidHom) := by
  rw [K1.mapRingHom_mk, K1.detHom_mk, Matrix.GeneralLinearGroup.det_mapRingHom]
  rfl

/-- Three literal field worlds retain the original field-unit computation of every source class. -/
theorem three_world_field_dictionary {F : Type uR} {E : Type uS} {L : Type uT}
    [Field F] [Field E] [Field L] (φ : F →+* E) (ψ : E →+* L) (a : K1 F) :
    K1.detEquivUnitsOfField (F := L) (K1.mapRingHom ψ (K1.mapRingHom φ a)) =
      (Units.map ψ.toMonoidHom).toAdditive
        ((Units.map φ.toMonoidHom).toAdditive (K1.detEquivUnitsOfField (F := F) a)) := by
  rw [K1.detEquivUnitsOfField_mapRingHom, K1.detEquivUnitsOfField_mapRingHom]

/-- The native field coefficient map is computed on the actual old inverse unit dictionary. -/
theorem field_inverse_dictionary {F : Type uR} {E : Type uS} [Field F] [Field E]
    (φ : F →+* E) (a : Additive Fˣ) :
    K1.mapRingHom φ ((K1.detEquivUnitsOfField (F := F)).symm a) =
      (K1.detEquivUnitsOfField (F := E)).symm
        ((Units.map φ.toMonoidHom).toAdditive a) := by
  apply (K1.detEquivUnitsOfField (F := E)).injective
  rw [K1.detEquivUnitsOfField_mapRingHom, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

end MathlibExtTest.KTheory.Ring.K1.DeterminantScalarMapTests

end
