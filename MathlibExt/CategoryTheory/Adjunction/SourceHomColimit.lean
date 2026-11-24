/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Source Hom preserves a given colimit through an actual adjunction

The source and target Hom universes remain independent. Only the given
diagram and its actual right-adjoint/source-Hom preservation are assumed.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe t vT vC vD uC uD

open CategoryTheory Limits Opposite

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  {T : Type t} [Category.{vT} T]
  {L : C ⥤ D} {R : D ⥤ C}

/-- Source Hom for the actual left-adjoint object preserves the given colimit. -/
theorem preservesColimit_leftAdjointSource
    (adj : L ⊣ R) (A : C) (F : T ⥤ D)
    [PreservesColimit F R]
    [PreservesColimit (F ⋙ R) (coyoneda.obj (op A))] :
    PreservesColimit F (coyoneda.obj (op (L.obj A))) := by
  let HC : C ⥤ Type vC := coyoneda.obj (op A)
  let HD : D ⥤ Type vD := coyoneda.obj (op (L.obj A))
  let UC : Type vC ⥤ Type (max vC vD) := uliftFunctor.{vD, vC}
  let UD : Type vD ⥤ Type (max vC vD) := uliftFunctor.{vC, vD}
  let _ : PreservesColimit F (R ⋙ HC) := inferInstance
  let _ : PreservesColimit F ((R ⋙ HC) ⋙ UC) := inferInstance
  let e : (R ⋙ HC) ⋙ UC ≅ HD ⋙ UD :=
    (adj.compUliftCoyonedaIso.{0}.app (op A)).symm
  let _ : PreservesColimit F (HD ⋙ UD) := preservesColimit_of_natIso F e
  exact preservesColimit_of_reflects_of_preserves HD UD

/-- The original caller's colimit cocone remains colimit after source Hom. -/
def isColimitLeftAdjointSource
    (adj : L ⊣ R) (A : C) (F : T ⥤ D)
    [PreservesColimit F R]
    [PreservesColimit (F ⋙ R) (coyoneda.obj (op A))]
    (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((coyoneda.obj (op (L.obj A))).mapCocone c) := by
  let _ : PreservesColimit F (coyoneda.obj (op (L.obj A))) :=
    adj.preservesColimit_leftAdjointSource A F
  exact isColimitOfPreserves (coyoneda.obj (op (L.obj A))) hc


/-- Deprecated alias retaining the original public colimit map. -/
@[deprecated isColimitLeftAdjointSource (since := "2026-11-06"), nolint defsWithUnderscore]
alias isColimit_leftAdjointSource := isColimitLeftAdjointSource

end CategoryTheory.Adjunction
