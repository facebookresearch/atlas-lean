/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCofiber
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyFiber

/-!
# Generic derived suspension and loop functors

In a model category with a zero object, derived suspension is the reviewed
homotopy cofiber of `X ⟶ 0`, and derived loop is the reviewed homotopy fiber
of `0 ⟶ X`. Both constructions preserve weak equivalences functorially.

No suspension-loop adjunction, unit, counit, equivalence, localization,
framing theorem, or selected TopCat/SSet instance is claimed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty
open scoped ZeroObject

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable [HasZeroObject C]

section Suspension

variable [HasFunctorialFactorization
  (cofibrations C) (trivialFibrations C)]

/-- Derived suspension, as the homotopy cofiber of the canonical arrow
`X ⟶ 0`. -/
noncomputable def derivedSuspension : C ⥤ C where
  obj X := (homotopyCofiber (C := C)).obj
    (Arrow.mk (HasZeroObject.zeroIsTerminal.from X))
  map {X Y} f := (homotopyCofiber (C := C)).map
    (Arrow.homMk f (𝟙 (0 : C)) (by
      apply HasZeroObject.zeroIsTerminal.hom_ext))
  map_id X := by
    rw [show Arrow.homMk (𝟙 X) (𝟙 (0 : C)) =
        𝟙 (Arrow.mk (HasZeroObject.zeroIsTerminal.from X)) by
      ext <;> simp]
    exact (homotopyCofiber (C := C)).map_id _
  map_comp {X Y Z} f g := by
    rw [← (homotopyCofiber (C := C)).map_comp]
    apply congrArg
    ext <;> simp

@[simp]
theorem derivedSuspension_obj (X : C) :
    (derivedSuspension (C := C)).obj X =
      (homotopyCofiber (C := C)).obj
        (Arrow.mk (HasZeroObject.zeroIsTerminal.from X)) :=
  rfl

/-- Derived suspension preserves weak equivalences. -/
theorem derivedSuspension_map_weakEquivalence
    {X Y : C} (f : X ⟶ Y) (hf : WeakEquivalence f) :
    WeakEquivalence ((derivedSuspension (C := C)).map f) := by
  apply homotopyCofiber_map_weakEquivalence
  · exact hf
  · change WeakEquivalence (𝟙 (0 : C))
    infer_instance

end Suspension

section Loop

variable [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)]

/-- Derived loop, as the homotopy fiber of the canonical arrow `0 ⟶ X`. -/
noncomputable def derivedLoop : C ⥤ C where
  obj X := (homotopyFiber (C := C)).obj
    (Arrow.mk (HasZeroObject.zeroIsInitial.to X))
  map {X Y} f := (homotopyFiber (C := C)).map
    (Arrow.homMk (𝟙 (0 : C)) f (by
      apply HasZeroObject.zeroIsInitial.hom_ext))
  map_id X := by
    rw [show Arrow.homMk (𝟙 (0 : C)) (𝟙 X) =
        𝟙 (Arrow.mk (HasZeroObject.zeroIsInitial.to X)) by
      ext <;> simp]
    exact (homotopyFiber (C := C)).map_id _
  map_comp {X Y Z} f g := by
    rw [← (homotopyFiber (C := C)).map_comp]
    apply congrArg
    ext <;> simp

@[simp]
theorem derivedLoop_obj (X : C) :
    (derivedLoop (C := C)).obj X =
      (homotopyFiber (C := C)).obj
        (Arrow.mk (HasZeroObject.zeroIsInitial.to X)) :=
  rfl

/-- Derived loop preserves weak equivalences. -/
theorem derivedLoop_map_weakEquivalence
    {X Y : C} (f : X ⟶ Y) (hf : WeakEquivalence f) :
    WeakEquivalence ((derivedLoop (C := C)).map f) := by
  apply homotopyFiber_map_weakEquivalence
  · change WeakEquivalence (𝟙 (0 : C))
    infer_instance
  · exact hf

end Loop

end HomotopicalAlgebra
