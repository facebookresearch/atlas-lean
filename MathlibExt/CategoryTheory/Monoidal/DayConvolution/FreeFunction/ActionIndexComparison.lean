/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braiding the coefficient and shift indices

In a symmetric monoidal index, compares the two associations of the coefficient and shift
factors. Its braid satisfies the prescribed right-order formula with the associator and
component braiding maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory.CoefficientIndexBraiding
variable {I : Type u} [Category.{v} I] [MonoidalCategory I] [SymmetricCategory I]

/-- The original free-source index passes the complete coefficient block through the source block
with the genuine braiding and both original associators. -/
def leftCoefficientComparison (r a n : I) : a ⊗ (r ⊗ n) ≅ r ⊗ (a ⊗ n) :=
  (α_ a r n).symm ≪≫ whiskerRightIso (β_ a r) n ≪≫ α_ r a n

/-- Original first-factor coefficient transport followed by the actual beta_(r,a tensor n) is the
complete final-factor shifted coefficient transport. -/
theorem rightOrder (r a n : I) :
    (leftCoefficientComparison r a n).hom ≫ (β_ r (a ⊗ n)).hom =
      (a ◁ (β_ r n).hom) ≫ (α_ a n r).inv := by
  simp only [leftCoefficientComparison, Iso.trans_hom, Iso.symm_hom,
    whiskerRightIso_hom, BraidedCategory.braiding_tensor_right_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry, id_whiskerRight,
    Category.id_comp, Iso.inv_hom_id_assoc]

end CategoryTheory.MonoidalCategory.CoefficientIndexBraiding
