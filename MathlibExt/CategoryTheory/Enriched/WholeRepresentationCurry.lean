/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Enriched.WholeRepresentationData
public import MathlibExt.CategoryTheory.Enriched.GradedYoneda

/-!
# Curry and uncurry for complete enriched representations

The actual closed adjunction turns the entire action into an enriched Hom
map. Its composition law retains every full Hom object.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV uC

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.WholeRepresentation

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]

/-- The actual enriched functor whose full Hom maps are the transposed original actions. -/
def toEnrichedFunctor (X : WholeRepresentation V C) : EnrichedFunctor V C V where
  obj := X.obj
  map x y := MonoidalClosed.curry (X.action x y)
  map_id x := by
    apply MonoidalClosed.uncurry_injective
    change MonoidalClosed.uncurry (eId V x ≫ MonoidalClosed.curry (X.action x x)) =
      MonoidalClosed.uncurry (MonoidalClosed.curry (ρ_ (X.obj x)).hom)
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
      MonoidalClosed.uncurry_curry]
    exact X.unit x
  map_comp x y z := by
    apply MonoidalClosed.uncurry_injective
    change MonoidalClosed.uncurry (eComp V x y z ≫ MonoidalClosed.curry (X.action x z)) =
      MonoidalClosed.uncurry ((MonoidalClosed.curry (X.action x y) ⊗ₘ
        MonoidalClosed.curry (X.action y z)) ≫ eComp V (X.obj x) (X.obj y) (X.obj z))
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
      MonoidalClosed.uncurry_eComp, MonoidalClosed.uncurry_curry,
      MonoidalClosed.uncurry_curry]
    exact (X.assoc x y z).symm

/-- Every original enriched functor gives its full uncurried action representation. -/
def ofEnrichedFunctor (F : EnrichedFunctor V C V) : WholeRepresentation V C where
  obj := F.obj
  action x y := MonoidalClosed.uncurry (F.map x y)
  unit x := by
    rw [← MonoidalClosed.uncurry_natural_left, F.map_id]
    exact MonoidalClosed.uncurry_curry _
  assoc x y z := by
    have h := congrArg MonoidalClosed.uncurry (F.map_comp x y z)
    change MonoidalClosed.uncurry (eComp V x y z ≫ F.map x z) =
      MonoidalClosed.uncurry ((F.map x y ⊗ₘ F.map y z) ≫
        eComp V (F.obj x) (F.obj y) (F.obj z)) at h
    rw [MonoidalClosed.uncurry_eComp, MonoidalClosed.uncurry_natural_left] at h
    exact h.symm

/-- The original object function is unchanged by currying. -/
theorem toEnrichedFunctor_obj (X : WholeRepresentation V C) (x : C) :
    X.toEnrichedFunctor.obj x = X.obj x := rfl

/-- The entire Hom map is the actual transpose of the original action. -/
theorem toEnrichedFunctor_map (X : WholeRepresentation V C) (x y : C) :
    X.toEnrichedFunctor.map x y = MonoidalClosed.curry (X.action x y) := rfl

/-- Every complete uncurried action is recovered from the transposed functor. -/
theorem of_to_action (X : WholeRepresentation V C) (x y : C) :
    (ofEnrichedFunctor X.toEnrichedFunctor).action x y = X.action x y :=
  MonoidalClosed.uncurry_curry _

/-- Every complete original enriched Hom map is recovered by curry after uncurry. -/
theorem to_of_map (F : EnrichedFunctor V C V) (x y : C) :
    (ofEnrichedFunctor F).toEnrichedFunctor.map x y = F.map x y :=
  MonoidalClosed.curry_uncurry _

end CategoryTheory.WholeRepresentation
