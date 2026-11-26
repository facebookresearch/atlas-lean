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
# The literal unitHom terminal enrichment on the fixed labels

The same label type, including the empty type, carries the
codiscrete terminal object of its fixed-object fibre. maps are
constructed by the scalar unit maps and retain every 
label. 
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.CodiscreteTerminal

variable (O : Type u)

/-- The terminal fixed-label object has the literal labels and scalar unit Homs. -/
def object : FixedObjects O := by
  letI := CodiscreteEnrichment.enrichment O
  exact FixedObjects.of O

/-- Every Hom is literally the scalar tensor unit. -/
theorem hom_object (x y : O) : hom (object O) x y = 𝟙_ SSet.{u} := rfl

variable {O}

/-- The terminal map uses the scalar maps to the unit. -/
def toTerminal (C : FixedObjects O) : C ⟶ object O :=
  ofHomMaps (fun x y => CodiscreteEnrichment.toUnit (hom C x y))
    (fun _ => (CartesianMonoidalCategory.isTerminalTensorUnit : IsTerminal (𝟙_
      SSet.{u})).hom_ext _ _)
    (fun _ _ _ => (CartesianMonoidalCategory.isTerminalTensorUnit : IsTerminal (𝟙_
      SSet.{u})).hom_ext _ _)

/-- Its Hom leg is the identical scalar map to the unit. -/
theorem toTerminal_homMap (C : FixedObjects O) (x y : O) :
    homMap (toTerminal C) x y = CodiscreteEnrichment.toUnit (hom C x y) :=
  homMap_ofHomMaps _ _ _ _ _

/-- Every individually supplied label is retained literally. -/
theorem toTerminal_vertex (C : FixedObjects O) (x : O) :
    (toTerminal C).val.obj (vertex C x) = x := map_vertex _ _

/-- There is exactly one fixed-label map into the unitHom object. -/
theorem toTerminal_unique (C : FixedObjects O) (f : C ⟶ object O) : f = toTerminal C := by
  apply homMaps_ext
  intro x y
  exact (CartesianMonoidalCategory.isTerminalTensorUnit : IsTerminal (𝟙_ SSet.{u})).hom_ext _ _

/-- The unitHom object is terminal in the exact fixed-label fibre. -/
def isTerminal : IsTerminal (object O) := IsTerminal.ofUniqueHom toTerminal toTerminal_unique

/-- The terminal map commutes with every fixed-label enriched functor. -/
theorem toTerminal_naturality {C D : FixedObjects O} (f : C ⟶ D) :
    f ≫ toTerminal D = toTerminal C := toTerminal_unique C _

end CategoryTheory.SimplicialEnrichment.FixedObjects.CodiscreteTerminal
