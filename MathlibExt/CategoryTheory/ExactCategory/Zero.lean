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

public import MathlibExt.CategoryTheory.ExactCategory.Basic

/-!
# Zero legs in admissible exact sequences

For an arbitrary zero object `Z`, the literal short complexes
`Z ⟶ B ⟶ B` with legs `0, 𝟙` and `A ⟶ A ⟶ Z` with legs
`𝟙, 0` are admissible exact.  The proofs transport the split admissible
exact sequence across the canonical zero-biproduct isomorphism; the public
complexes themselves retain their literal objects and maps.

An admissible exact sequence with zero source has invertible second map, and
dually one with zero target has invertible first map.  These follow directly
from the cokernel and kernel universal properties, without a
balanced-category assumption.

This file defines no extension-stage construction, homotopy, realization,
or additivity result.
-/

@[expose] public section

open CategoryTheory Limits Preadditive ZeroObject

universe v u

namespace CategoryTheory.ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- For any zero object `Z`, the literal short complex `Z → B → B`
with maps `0` and `𝟙 B` is admissible exact. -/
theorem isAdmissibleExact_zero_id {Z B : C} (hZ : IsZero Z) :
    IsAdmissibleExact
      (ShortComplex.mk (0 : Z ⟶ B) (𝟙 B) (by simp)) := by
  let S_split : ShortComplex C :=
    ShortComplex.mk (biprod.inl : Z ⟶ Z ⊞ B)
      (biprod.snd : Z ⊞ B ⟶ B) (by simp)
  have h_split : IsAdmissibleExact S_split :=
    isAdmissibleExact_split Z B
  have h_iso :
      ShortComplex.mk (0 : Z ⟶ B) (𝟙 B) (by simp) ≅ S_split :=
    ShortComplex.isoMk (Iso.refl Z) (isoZeroBiprod hZ) (Iso.refl B)
      (hZ.eq_of_src _ _) (by dsimp [S_split]; simp)
  exact isAdmissibleExact_of_iso h_iso.symm h_split

/-- For any zero object `Z`, the literal short complex `A → A → Z`
with maps `𝟙 A` and `0` is admissible exact. -/
theorem isAdmissibleExact_id_zero {A Z : C} (hZ : IsZero Z) :
    IsAdmissibleExact
      (ShortComplex.mk (𝟙 A) (0 : A ⟶ Z) (by simp)) := by
  let S_split : ShortComplex C :=
    ShortComplex.mk (biprod.inl : A ⟶ A ⊞ Z)
      (biprod.snd : A ⊞ Z ⟶ Z) (by simp)
  have h_split : IsAdmissibleExact S_split :=
    isAdmissibleExact_split A Z
  have h_iso :
      ShortComplex.mk (𝟙 A) (0 : A ⟶ Z) (by simp) ≅ S_split :=
    ShortComplex.isoMk (Iso.refl A) (isoBiprodZero hZ) (Iso.refl Z)
      (by dsimp [S_split]; simp) (hZ.eq_of_tgt _ _)
  exact isAdmissibleExact_of_iso h_iso.symm h_split

/-- If the source of an admissible exact sequence is zero, then its second
map is an isomorphism.  No `Balanced C` assumption is needed: the second map
is a cokernel of the zero first map. -/
theorem isIso_g_of_isAdmissibleExact_of_isZero {S : ShortComplex C}
    (hS : IsAdmissibleExact S) (hX₁ : IsZero S.X₁) : IsIso S.g := by
  have hc : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
    isColimit_cokernelCofork_of_isAdmissibleExact hS
  exact CokernelCofork.IsColimit.isIso_π
    (CokernelCofork.ofπ S.g S.zero) hc (hX₁.eq_of_src S.f 0)

/-- If the target of an admissible exact sequence is zero, then its first
map is an isomorphism.  No `Balanced C` assumption is needed: the first map
is a kernel of the zero second map. -/
theorem isIso_f_of_isAdmissibleExact_of_isZero {S : ShortComplex C}
    (hS : IsAdmissibleExact S) (hX₃ : IsZero S.X₃) : IsIso S.f := by
  have hk : IsLimit (KernelFork.ofι S.f S.zero) :=
    isLimit_kernelFork_of_isAdmissibleExact hS
  exact KernelFork.IsLimit.isIso_ι
    (KernelFork.ofι S.f S.zero) hk (hX₃.eq_of_tgt S.g 0)

end CategoryTheory.ExactCategory
