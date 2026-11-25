/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.HoInverse

/-!
# Public use of categorical homotopy inverses

The neutral import supplies an actual inverse map and both inverse
isomorphisms. The first triangle can be transported by an arbitrary
simplicial map while retaining the same inverse and the second triangle.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalClosed
open scoped Simplicial

universe u

namespace HoInverseTest

open SSet

variable {X Y Z : SSet.{u}} {f : X ⟶ Y}
variable [Quasicategory X] [Quasicategory Y]

/-- The public theorem provides actual map and isomorphism witnesses. -/
def inverseData (hf : categoricalEquivalences f) :
    Σ g : Y ⟶ X,
      (HomotopyCategory.mk (ihomVertexEquiv X X (f ≫ g)) ≅
        HomotopyCategory.mk (ihomVertexEquiv X X (𝟙 X))) ×
      (HomotopyCategory.mk (ihomVertexEquiv Y Y (g ≫ f)) ≅
        HomotopyCategory.mk (ihomVertexEquiv Y Y (𝟙 Y))) := by
  let H := hf.hasHoInverse
  exact ⟨H.choose, Classical.choice H.choose_spec.1, Classical.choice H.choose_spec.2⟩

/-- Postcomposition preserves the first triangle and its shared inverse map. -/
theorem transport_first_triangle (hf : categoricalEquivalences f) (q : X ⟶ Z) :
    ∃ g : Y ⟶ X,
      Nonempty (HomotopyCategory.mk (ihomVertexEquiv X Z (f ≫ g ≫ q)) ≅
        HomotopyCategory.mk (ihomVertexEquiv X Z q)) ∧
      Nonempty (HomotopyCategory.mk (ihomVertexEquiv Y Y (g ≫ f)) ≅
        HomotopyCategory.mk (ihomVertexEquiv Y Y (𝟙 Y))) := by
  obtain ⟨g, ⟨α⟩, ⟨β⟩⟩ := hf.hasHoInverse
  have h := (mapHomotopyCategory ((ihom X).map q)).mapIso α
  rw [mapHomotopyCategory_obj_mk, mapHomotopyCategory_obj_mk,
    ihomVertexEquiv_ihom_map, ihomVertexEquiv_ihom_map] at h
  rw [Category.id_comp, Category.assoc] at h
  exact ⟨g, ⟨h⟩, ⟨β⟩⟩

end HoInverseTest
