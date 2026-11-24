/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CodiscreteEnrichment
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomMaps

/-!
# The literal unit-Hom terminal enrichment on the original fixed labels

The same original label type, including the empty type, carries the
codiscrete terminal object of its fixed-object fibre. Whole maps are
constructed by the actual scalar unit maps and retain every original
label. No model or weakness statement is part of this neutral adapter.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.CodiscreteTerminal

variable (O : Type u)

/-- The terminal fixed-label object has the literal original labels and scalar unit Homs. -/
def object : FixedObjects O := by
  letI := CodiscreteEnrichment.enrichment O
  exact FixedObjects.of O

/-- Every original Hom is literally the scalar tensor unit. -/
theorem hom_object (x y : O) : hom (object O) x y = 𝟙_ SSet.{u} := rfl

variable {O}

/-- The whole actual terminal map uses the original scalar maps to the unit. -/
def toTerminal (C : FixedObjects O) : C ⟶ object O :=
  ofHomMaps (fun x y => CodiscreteEnrichment.toUnit (hom C x y))
    (fun _ => (CartesianMonoidalCategory.isTerminalTensorUnit : IsTerminal (𝟙_
      SSet.{u})).hom_ext _ _)
    (fun _ _ _ => (CartesianMonoidalCategory.isTerminalTensorUnit : IsTerminal (𝟙_
      SSet.{u})).hom_ext _ _)

/-- Its original Hom leg is the identical whole scalar map to the unit. -/
theorem toTerminal_homMap (C : FixedObjects O) (x y : O) :
    homMap (toTerminal C) x y = CodiscreteEnrichment.toUnit (hom C x y) :=
  homMap_ofHomMaps _ _ _ _ _

/-- Every individually supplied original label is retained literally. -/
theorem toTerminal_vertex (C : FixedObjects O) (x : O) :
    (toTerminal C).val.obj (vertex C x) = x := map_vertex _ _

/-- There is exactly one whole original fixed-label map into the unit-Hom object. -/
theorem toTerminal_unique (C : FixedObjects O) (f : C ⟶ object O) : f = toTerminal C := by
  apply homMaps_ext
  intro x y
  exact (CartesianMonoidalCategory.isTerminalTensorUnit : IsTerminal (𝟙_ SSet.{u})).hom_ext _ _

/-- The actual unit-Hom object is terminal in the exact original fixed-label fibre. -/
def isTerminal : IsTerminal (object O) := IsTerminal.ofUniqueHom toTerminal toTerminal_unique

/-- The actual terminal map commutes with every whole original fixed-label enriched functor. -/
theorem toTerminal_naturality {C D : FixedObjects O} (f : C ⟶ D) :
    f ≫ toTerminal D = toTerminal C := toTerminal_unique C _

end CategoryTheory.SimplicialEnrichment.FixedObjects.CodiscreteTerminal
