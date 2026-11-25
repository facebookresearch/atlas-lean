/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.TopMarkedCylinder

/-!
# Whole original functoriality of the top-marked cylinder

Every original marked coefficient map acts on the entire original
product and keeps the interval coordinate fixed. Original marked
product edges and every added original top-edge image are preserved.
Both original inclusions and whole pushout descents are natural in the
same actual marked coefficient maps.
-/

noncomputable section
universe u
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace SSet.Marked

/-- Original marked coefficient maps retain the whole interval coordinate and actual maximally marked top layer. -/
def topMarkedCylinderMap {A B : Marked.{u}} (f : A ⟶ B) : topMarkedCylinder A ⟶ topMarkedCylinder B where
  hom := f.hom ⊗ₘ 𝟙 (Δ[1] : SSet.{u})
  preserve {e} he := by
    rcases he with h | ⟨a, rfl⟩
    · exact Or.inl ((prodMap f (𝟙 (min (Δ[1] : SSet.{u})))).preserve h)
    · refine Or.inr ⟨f.hom.app (op ⦋1⦌) a, ?_⟩
      rfl

/-- The actual top marking upgrade is a native functor on the original marked carrier. -/
def topMarkedCylinderFunctor : Marked.{u} ⥤ Marked.{u} where
  obj := topMarkedCylinder
  map := topMarkedCylinderMap
  map_id A := by apply Hom.ext; ext q z; rfl
  map_comp f g := by apply Hom.ext; ext q z; rfl

/-- Each whole original minimal-product inclusion commutes with the same original coefficient map. -/
theorem topMarkedCylinderInl_natural {A B : Marked.{u}} (f : A ⟶ B) :
    prodMap f (𝟙 (min (Δ[1] : SSet.{u}))) ≫ topMarkedCylinderInl B =
      topMarkedCylinderInl A ≫ topMarkedCylinderMap f := Hom.ext rfl

/-- The complete maximally marked top inclusion retains the original coefficient map and full interval simplex. -/
theorem topMarkedCylinderInr_natural {A B : Marked.{u}} (f : A ⟶ B) :
    maximal.map f.hom ≫ topMarkedCylinderInr B =
      topMarkedCylinderInr A ≫ topMarkedCylinderMap f := by
  apply Hom.ext
  ext q z
  apply Prod.ext <;> rfl

end SSet.Marked
