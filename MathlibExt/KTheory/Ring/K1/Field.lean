/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Field
public import MathlibExt.KTheory.Ring.K1.Local

/-! # K₁ of a field via determinant -/

@[expose] public section

universe u

namespace AlgebraicKTheory

noncomputable section

variable (F : Type u) [Field F]

/-- Stable elementary subgroup equals the kernel of the stable determinant over a field. -/
theorem stableElementarySubgroup_eq_ker_det_of_field :
    stableElementarySubgroup F = MonoidHom.ker (StableGL.det (R := F)) :=
  stableElementarySubgroup_eq_ker_det_of_isLocalRing F

/-- Determinant on `K₁` is injective over a field. -/
theorem K1.detHom_injective_of_field :
    Function.Injective (K1.detHom (R := F)) :=
  K1.detHom_injective_of_isLocalRing F

/-- Determinant equivalence `K₁ F ≃+ Additive Fˣ` for a field. -/
noncomputable def K1.detEquivUnitsOfField :
    K1 F ≃+ Additive Fˣ :=
  K1.detEquivUnitsOfLocalRing (R := F)

@[simp]
theorem K1.detEquivUnitsOfField_apply (x : K1 F) :
    K1.detEquivUnitsOfField (F := F) x = K1.detHom (R := F) x :=
  rfl

end

end AlgebraicKTheory

end
