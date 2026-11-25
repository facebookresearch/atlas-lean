/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/DayConvolution/Unit.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor

/-!
# Values of the Day convolution unit

The unit `𝟙_ (C ⊛⥤ V)` of the Day convolution monoidal structure is the left Kan extension of
`𝟙_ V` along the inclusion of `𝟙_ C`, so its value at `d : C` is the colimit of the constant
diagram `𝟙_ V` indexed by the morphisms `𝟙_ C ⟶ d`. We compute this value in the two extreme
cases:

* when `𝟙_ C` has no endomorphism other than the identity, Mathlib's canonical map
  `ν : 𝟙_ V ⟶ (𝟙_ (C ⊛⥤ V)).functor.obj (𝟙_ C)` is an isomorphism;
* when there is no morphism `𝟙_ C ⟶ d`, the value at `d` is an initial object.

For the finite-bijection groupoid both cases apply: the unit symmetric sequence is `𝟙_ V` in
level zero and initial in every positive level.

## Main statements

* `DayFunctor.isIso_ν`: `ν` is an isomorphism when `𝟙_ C` has only the identity endomorphism.
* `DayFunctor.isInitialUnitObj`: the unit is initial at objects receiving no morphism from
  `𝟙_ C`.
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.MonoidalCategory.DayFunctor

open scoped ExternalProduct
open Limits LawfulDayConvolutionMonoidalCategoryStruct

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape
      (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape
      (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

/-- If the only endomorphism of `𝟙_ C` is the identity, then the canonical map
`ν : 𝟙_ V ⟶ (𝟙_ (C ⊛⥤ V)).functor.obj (𝟙_ C)` is an isomorphism: the Day convolution unit takes
the value `𝟙_ V` at `𝟙_ C`. -/
instance isIso_ν [Subsingleton (𝟙_ C ⟶ 𝟙_ C)] : IsIso (ν C V) := by
  have : (Functor.fromPUnit.{0} (𝟙_ C)).Full :=
    ⟨fun _ ↦ ⟨Discrete.eqToHom (Subsingleton.elim _ _), Subsingleton.elim (α := 𝟙_ C ⟶ 𝟙_ C) _ _⟩⟩
  exact (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ (νNatTrans C V)
    (𝟙_ C)).isIso_hom_app (X := ⟨⟨⟩⟩)

/-- If there is no morphism `𝟙_ C ⟶ d`, then the Day convolution unit takes an initial value
at `d`. -/
def isInitialUnitObj {d : C} [IsEmpty (𝟙_ C ⟶ d)] :
    IsInitial ((𝟙_ (C ⊛⥤ V)).functor.obj d) :=
  have : IsEmpty (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) :=
    ⟨fun f ↦ IsEmpty.false (α := 𝟙_ C ⟶ d) f.hom⟩
  isColimitEquivIsInitialOfIsEmpty _ _
    (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ (νNatTrans C V) d)

end

end CategoryTheory.MonoidalCategory.DayFunctor
