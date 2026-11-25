/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.ModelCategory.Monoidal
public import MathlibExt.CategoryTheory.Monoidal.PushoutProductInitial
public import MathlibExt.CategoryTheory.Monoidal.TensorPowers
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Cofibrant tensor products and finite tensor powers

The pushout-product law and preservation of the required initial objects
give cofibrant tensor products and finite tensor powers. A corresponding
law for an isomorphism-stable map property gives its preservation by
fixed-left tensor. The final lemmas apply these results to the selected
closed symmetric monoidal model structure.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Cofibrations

variable [CategoryWithCofibrations C] [HasInitial C] [HasPushouts C]
  [(cofibrations C).RespectsIso]

/-- The actual pushout-product law gives cofibrancy of a tensor product. -/
theorem isCofibrant_tensorObj_of_pushoutProduct
    (hPP : PushoutProductLe (cofibrations C) (cofibrations C) (cofibrations C))
    (X Y : C) [IsCofibrant X] [IsCofibrant Y]
    [PreservesColimit (Functor.empty.{0} C) (tensorLeft (⊥_ C))]
    [PreservesColimit (Functor.empty.{0} C) (tensorLeft X)]
    [PreservesColimit (Functor.empty.{0} C) (tensorRight Y)] :
    IsCofibrant (X ⊗ Y) := by
  let h₀ : IsInitial ((⊥_ C) ⊗ (⊥_ C)) :=
    IsInitial.isInitialObj (tensorLeft (⊥_ C)) (⊥_ C) initialIsInitial
  let hX : IsInitial (X ⊗ (⊥_ C)) :=
    IsInitial.isInitialObj (tensorLeft X) (⊥_ C) initialIsInitial
  let hY : IsInitial ((⊥_ C) ⊗ Y) :=
    IsInitial.isInitialObj (tensorRight Y) (⊥_ C) initialIsInitial
  have hp : IsInitial
      ((Arrow.mk (initial.to X) □ Arrow.mk (initial.to Y)).left) := by
    change IsInitial
      (pushout (initial.to X ▷ (⊥_ C)) ((⊥_ C) ◁ initial.to Y))
    apply IsInitial.ofUniqueHom
      (fun Z ↦ pushout.desc (hX.to Z) (hY.to Z) (h₀.hom_ext _ _))
    intro Z f
    exact pushout.hom_ext (hX.hom_ext _ _) (hY.hom_ext _ _)
  have hbox := hPP (initial.to X) (initial.to Y)
    ((cofibration_iff _).mp inferInstance)
    ((cofibration_iff _).mp inferInstance)
  exact (isCofibrant_iff_of_isInitial
    (Arrow.mk (initial.to X) □ Arrow.mk (initial.to Y)).hom hp).mpr
      ((cofibration_iff _).mpr hbox)

/-- Literal finite tensor powers are cofibrant when the unit and coordinate
are cofibrant and the required tensor functors preserve initial objects. -/
theorem isCofibrant_tensorPowObj_of_pushoutProduct
    (hPP : PushoutProductLe (cofibrations C) (cofibrations C) (cofibrations C))
    (K : C) [IsCofibrant K] [IsCofibrant (𝟙_ C)]
    [PreservesColimit (Functor.empty.{0} C) (tensorLeft (⊥_ C))]
    [∀ n : ℕ, PreservesColimit (Functor.empty.{0} C)
      (tensorLeft (TensorPower.tensorPowObj K n))]
    [PreservesColimit (Functor.empty.{0} C) (tensorRight K)]
    (r : ℕ) :
    IsCofibrant (TensorPower.tensorPowObj K r) := by
  induction r with
  | zero =>
      change IsCofibrant (𝟙_ C)
      infer_instance
  | succ r ih =>
      let _ : IsCofibrant (TensorPower.tensorPowObj K r) := ih
      let _ : PreservesColimit (Functor.empty.{0} C)
          (tensorLeft (TensorPower.tensorPowObj K r)) := inferInstance
      change IsCofibrant (TensorPower.tensorPowObj K r ⊗ K)
      exact isCofibrant_tensorObj_of_pushoutProduct hPP _ _

omit [(cofibrations C).RespectsIso] in
/-- Left tensor by a cofibrant object preserves an isomorphism-stable map
property with the displayed cofibration pushout-product law. -/
theorem whiskerLeft_mem_of_isCofibrant
    (P : MorphismProperty C) [P.RespectsIso]
    (hPP : PushoutProductLe (cofibrations C) P P)
    (K : C) [IsCofibrant K] {A B : C} (j : A ⟶ B)
    [PreservesColimit (Functor.empty.{0} C) (tensorRight A)]
    [PreservesColimit (Functor.empty.{0} C) (tensorRight B)]
    (hj : P j) : P (K ◁ j) := by
  have hbox := hPP (initial.to K) j
    ((cofibration_iff _).mp inferInstance) hj
  exact (P.arrow_mk_iso_iff
    (MonoidalCategory.Arrow.PushoutProduct.isInitialIsoOfTensor
      (Arrow.mk j) initialIsInitial (K := K)
      (IsInitial.isInitialObj (tensorRight A) (⊥_ C) initialIsInitial)
      (IsInitial.isInitialObj (tensorRight B) (⊥_ C) initialIsInitial))).mp hbox

end Cofibrations

section ModelCategory

variable [ModelCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

/-- Tensor products of cofibrant objects in the selected model structure
are cofibrant. -/
theorem IsClosedSymmetricMonoidalModelCategory.isCofibrant_tensorObj
    (X Y : C) [IsCofibrant X] [IsCofibrant Y] :
    IsCofibrant (X ⊗ Y) :=
  isCofibrant_tensorObj_of_pushoutProduct
    (IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct (C := C)) X Y

/-- A cofibrant tensor unit and coordinate give cofibrant finite powers
in the selected model structure. -/
theorem IsClosedSymmetricMonoidalModelCategory.isCofibrant_tensorPowObj
    (K : C) [IsCofibrant K] [IsCofibrant (𝟙_ C)] (r : ℕ) :
    IsCofibrant (TensorPower.tensorPowObj K r) := by
  let _ : ∀ n : ℕ, PreservesColimit (Functor.empty.{0} C)
      (tensorLeft (TensorPower.tensorPowObj K n)) :=
    fun _ ↦ inferInstance
  exact isCofibrant_tensorPowObj_of_pushoutProduct
    (IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct (C := C)) K r

/-- Left tensor by a cofibrant object preserves selected cofibrations. -/
theorem IsClosedSymmetricMonoidalModelCategory.whiskerLeft_mem_cofibrations
    (K : C) [IsCofibrant K] {A B : C} (j : A ⟶ B)
    (hj : cofibrations C j) : cofibrations C (K ◁ j) :=
  whiskerLeft_mem_of_isCofibrant (cofibrations C)
    (IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct (C := C)) K j hj

/-- Left tensor by a cofibrant object preserves selected trivial cofibrations. -/
theorem IsClosedSymmetricMonoidalModelCategory.whiskerLeft_mem_trivialCofibrations
    (K : C) [IsCofibrant K] {A B : C} (j : A ⟶ B)
    (hj : trivialCofibrations C j) : trivialCofibrations C (K ◁ j) :=
  whiskerLeft_mem_of_isCofibrant (trivialCofibrations C)
    (IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right (C := C)) K j hj

end ModelCategory

end HomotopicalAlgebra
