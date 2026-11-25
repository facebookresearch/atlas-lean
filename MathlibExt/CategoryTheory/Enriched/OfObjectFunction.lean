/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Enriched.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uC

open CategoryTheory MonoidalCategory

namespace CategoryTheory.EnrichedCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {A : Type uA} {C : Type uC} [EnrichedCategory V C]

/-- Restrict genuine enrichment along an actual object function; all laws are inherited. -/
@[instance_reducible]
def ofObjectFunction (f : A → C) : EnrichedCategory V A where
  Hom X Y := f X ⟶[V] f Y
  id X := eId V (f X)
  comp X Y Z := eComp V (f X) (f Y) (f Z)
  id_comp X Y := e_id_comp V (f X) (f Y)
  comp_id X Y := e_comp_id V (f X) (f Y)
  assoc W X Y Z := e_assoc V (f W) (f X) (f Y) (f Z)

/-- Restriction retains the entire original Hom object. -/
theorem ofObjectFunction_hom (f : A → C) (X Y : A) :
    (ofObjectFunction (V := V) f).Hom X Y = (f X ⟶[V] f Y) := by rfl

/-- Restriction retains the original identity morphism. -/
theorem ofObjectFunction_id (f : A → C) (X : A) :
    (ofObjectFunction (V := V) f).id X = eId V (f X) := by rfl

/-- Restriction retains the whole original composition morphism. -/
theorem ofObjectFunction_comp (f : A → C) (X Y Z : A) :
    (ofObjectFunction (V := V) f).comp X Y Z = eComp V (f X) (f Y) (f Z) := by rfl

end CategoryTheory.EnrichedCategory
