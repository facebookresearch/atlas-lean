/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.EnrichedAdjunctionFull

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uC vC uD

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.UnitGeneratedEnrichment

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory V C]
  {D : Type uD} [EnrichedCategory V D]

/-- Whole original point functions give the identity law for a map to the underlying category. -/
theorem map_id_of_point_function (F : C ⥤ ForgetEnrichment V D)
    (m : ∀ X Y : C, (X ⟶[V] Y) ⟶ (F.obj X ⟶[V] F.obj Y))
    (hp : ∀ X Y : C,
      (fun f : X ⟶ Y => eHomEquiv V f ≫ m X Y) =
        (fun f : X ⟶ Y => ForgetEnrichment.homTo V (F.map f))) (X : C) :
    eId V X ≫ m X X = eId V (F.obj X) := by
  have h := congrFun (hp X X) (𝟙 X)
  rw [eHomEquiv_id, F.map_id, ForgetEnrichment.homTo_id] at h
  exact h

variable [MonoidalClosed V]

/-- The full composition law follows from the original functor and entire point functions. -/
theorem map_comp_of_point_function (F : C ⥤ ForgetEnrichment V D)
    (hsep : IsSeparator (𝟙_ V))
    (m : ∀ X Y : C, (X ⟶[V] Y) ⟶ (F.obj X ⟶[V] F.obj Y))
    (hp : ∀ X Y : C,
      (fun f : X ⟶ Y => eHomEquiv V f ≫ m X Y) =
        (fun f : X ⟶ Y => ForgetEnrichment.homTo V (F.map f))) (X Y Z : C) :
    eComp V X Y Z ≫ m X Z =
      (m X Y ⊗ₘ m Y Z) ≫ eComp V (F.obj X) (F.obj Y) (F.obj Z) := by
  apply map_comp_of_points F hsep m
  intro X Y f
  exact congrFun (hp X Y) f

end CategoryTheory.UnitGeneratedEnrichment
