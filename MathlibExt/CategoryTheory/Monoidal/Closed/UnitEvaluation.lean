/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The original closed unit evaluation

The chosen closed unit comparison retains the original left unitor and evaluation.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uC vC uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

/- The characteristic below retains its original name and proof from
EnrichedAdjunctionValue.lean (historical authors: @toskua, Avocado). -/
namespace CategoryTheory.EnrichedAdjunctionHom.UnitValue

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [Closed (𝟙_ V)]

/-- The canonical closed-unit map uncurries to the actual left unitor. -/
theorem unitNatIso_hom_uncurry (Y : V) :
    MonoidalClosed.uncurry (MonoidalClosed.unitNatIso.hom.app Y) = (λ_ Y).hom := by
  simpa [MonoidalClosed.uncurry_eq, MonoidalClosed.unitNatIso] using
    (conjugateEquiv_counit (Adjunction.id (C := V)) (ihom.adjunction (𝟙_ V))
      (leftUnitorNatIso V).hom Y)

end CategoryTheory.EnrichedAdjunctionHom.UnitValue

namespace CategoryTheory.MonoidalClosed.UnitEvaluation
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [Closed (𝟙_ C)]

/-- The original public inverse API is the curry of the canonical closed-unit characteristic. -/
theorem inverse (Y : C) :
    MonoidalClosed.unitNatIso.hom.app Y = MonoidalClosed.curry (λ_ Y).hom := by
  apply MonoidalClosed.uncurry_injective
  rw [CategoryTheory.EnrichedAdjunctionHom.UnitValue.unitNatIso_hom_uncurry,
    MonoidalClosed.uncurry_curry]

/-- Its complete forward map is the original unit-Hom evaluation and
actual left unitor, with no alternative closed or unit data. -/
theorem forward (Y : C) :
    (MonoidalClosed.unitIsoSelf (X := Y)).hom =
      (λ_ ((ihom (𝟙_ C)).obj Y)).inv ≫ (ihom.ev (𝟙_ C)).app Y := by
  let J := (ihom (𝟙_ C)).obj Y
  let q : Y ⟶ J := MonoidalClosed.unitNatIso.hom.app Y
  let e : J ⟶ Y := (λ_ J).inv ≫ (ihom.ev (𝟙_ C)).app Y
  have he : q ≫ e = 𝟙 Y := by
    have hUnit := leftUnitor_inv_naturality q
    have hEval : MonoidalClosed.uncurry q = (λ_ Y).hom :=
      CategoryTheory.EnrichedAdjunctionHom.UnitValue.unitNatIso_hom_uncurry Y
    change q ≫ (λ_ J).inv ≫ (ihom.ev (𝟙_ C)).app Y = 𝟙 Y
    calc
      _ = (λ_ Y).inv ≫ ((𝟙_ C) ◁ q) ≫ (ihom.ev (𝟙_ C)).app Y := by
        have h := congrArg (fun z => z ≫ (ihom.ev (𝟙_ C)).app Y) hUnit
        simpa only [Category.assoc] using h
      _ = (λ_ Y).inv ≫ MonoidalClosed.uncurry q := by
        rw [MonoidalClosed.uncurry_eq]
      _ = (λ_ Y).inv ≫ (λ_ Y).hom := congrArg (fun z => (λ_ Y).inv ≫ z) hEval
      _ = _ := (λ_ Y).inv_hom_id
  apply (cancel_epi q).1
  exact ((MonoidalClosed.unitNatIso.app Y).hom_inv_id).trans he.symm

/-- Every complete map to the chosen unit cotensor evaluates by its
actual ordinary closed transpose, preserving the original unit comparison. -/
theorem map {X Y : C} (g : X ⟶ (ihom (𝟙_ C)).obj Y) :
    g ≫ (MonoidalClosed.unitIsoSelf (X := Y)).hom =
      (λ_ X).inv ≫ MonoidalClosed.uncurry g := by
  have he := forward Y
  have hUnit := leftUnitor_inv_naturality g
  calc
    _ = g ≫ ((λ_ ((ihom (𝟙_ C)).obj Y)).inv ≫ (ihom.ev (𝟙_ C)).app Y) :=
      congrArg (fun z => g ≫ z) he
    _ = (λ_ X).inv ≫ ((𝟙_ C) ◁ g) ≫ (ihom.ev (𝟙_ C)).app Y := by
      have h := congrArg (fun z => z ≫ (ihom.ev (𝟙_ C)).app Y) hUnit
      simpa only [Category.assoc] using h
    _ = _ := by rw [MonoidalClosed.uncurry_eq]

end CategoryTheory.MonoidalClosed.UnitEvaluation
