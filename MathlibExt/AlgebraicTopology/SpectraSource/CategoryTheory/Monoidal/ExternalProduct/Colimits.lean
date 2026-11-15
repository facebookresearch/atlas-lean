/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/ExternalProduct/Colimits.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Colimits of external products

External product with a fixed first diagram preserves colimits when tensoring with each
value of that diagram does. Colimits in functor categories are computed pointwise, so the
result follows by evaluating at a pair of objects. This supplies the colimit-preserving
input to the left Kan extension defining Day convolution.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.MonoidalCategory

variable {C C' V J : Type*} [Category* C] [Category* C'] [Category* V] [Category* J]
  [MonoidalCategory V]

/-- External product with a fixed first diagram preserves pointwise colimits if tensoring
with each of its values does. -/
instance preservesColimitsOfShape_externalProductLeft (F : C ⥤ V)
    [HasColimitsOfShape J V] [∀ x, PreservesColimitsOfShape J (tensorLeft (F.obj x))] :
    PreservesColimitsOfShape J
      ((externalProductBifunctorCurried C C' V).obj F ⋙ Functor.uncurry) := by
  apply preservesColimitsOfShape_of_evaluation
  intro p
  exact preservesColimitsOfShape_of_natIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) :
      (evaluation C' V).obj p.2 ⋙ tensorLeft (F.obj p.1) ≅
        ((externalProductBifunctorCurried C C' V).obj F ⋙ Functor.uncurry) ⋙
          (evaluation (C × C') V).obj p)

end CategoryTheory.MonoidalCategory
