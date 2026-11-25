/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Pointed comonoid transport by an oplax monoidal functor

The native oplax monoidal functor already maps comonoids. Its unit-image
counit is the canonical morphism to the trivial comonoid. When the original
oplax unit comparison is invertible, its native comonoid isomorphism supplies
the point map. Native `Under.post` and `Under.map` assemble the resulting
functor. Tensor comparisons need not be invertible.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory
open scoped ComonObj

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.OplaxMonoidal]

/-- The existing canonical counit from the native image of the trivial comonoid. -/
def unitImageCounit : F.mapComon.obj (Comon.trivial C) ⟶ Comon.trivial D := default

/-- The underlying map is exactly the original oplax unit comparison. -/
theorem unitImageCounit_hom :
    (unitImageCounit F).hom = OplaxMonoidal.η F := by
  change F.map (𝟙 (𝟙_ C)) ≫ OplaxMonoidal.η F = OplaxMonoidal.η F
  rw [F.map_id, Category.id_comp]

variable [IsIso (OplaxMonoidal.η F)]

/-- The original invertible unit comparison is a native comonoid isomorphism by its counit law. -/
def unitImageComonIso : F.mapComon.obj (Comon.trivial C) ≅ Comon.trivial D := by
  let f := unitImageCounit F
  have hη : IsIso (OplaxMonoidal.η F) := inferInstance
  letI : IsIso f.hom := by
    exact (unitImageCounit_hom F).symm ▸ hη
  let e : (F.mapComon.obj (Comon.trivial C)).X ≅ (Comon.trivial D).X := asIso f.hom
  exact Comon.mkIso e f.isComonHom_hom.hom_counit f.isComonHom_hom.hom_comul

/-- The native comonoid comparison has the original oplax unit map as its forward map. -/
theorem unitImageComonIso_hom_hom :
    (unitImageComonIso F).hom.hom = OplaxMonoidal.η F := unitImageCounit_hom F

/-- The actual inverse point map is the inverse of the original oplax unit comparison. -/
theorem unitImageComonIso_inv_hom :
    (unitImageComonIso F).inv.hom = CategoryTheory.inv (OplaxMonoidal.η F) := by
  let g : 𝟙_ D ⟶ F.obj (𝟙_ C) := (unitImageComonIso F).inv.hom
  have h : g ≫ OplaxMonoidal.η F = 𝟙 (𝟙_ D) := by
    have hi := congrArg (fun f => f.hom) (unitImageComonIso F).inv_hom_id
    change g ≫ (unitImageComonIso F).hom.hom = 𝟙 (𝟙_ D) at hi
    exact (congrArg (fun f : F.obj (𝟙_ C) ⟶ 𝟙_ D => g ≫ f)
      (unitImageComonIso_hom_hom F)).symm.trans hi
  change g = CategoryTheory.inv (OplaxMonoidal.η F)
  exact (cancel_mono (OplaxMonoidal.η F)).1
    (h.trans (CategoryTheory.IsIso.inv_hom_id (OplaxMonoidal.η F)).symm)

/-- Native Under transport maps actual coaugmented comonoids with independent ambient universes. -/
def mapPointedComon : Under (Comon.trivial C) ⥤ Under (Comon.trivial D) :=
  Under.post F.mapComon ⋙ Under.map (unitImageComonIso F).inv

/-- The transported point is the original point image preceded by the inverse unit comparison. -/
theorem mapPointedComon_obj_point (A : Under (Comon.trivial C)) :
    (F.mapPointedComon.obj A).hom.hom = CategoryTheory.inv (OplaxMonoidal.η F) ≫
      F.map A.hom.hom := by
  change (unitImageComonIso F).inv.hom ≫ F.map A.hom.hom = _
  rw [unitImageComonIso_inv_hom]
  rfl

/-- The whole pointed morphism is exactly the native functor image of the original morphism. -/
theorem mapPointedComon_map_hom {A B : Under (Comon.trivial C)} (f : A ⟶ B) :
    (F.mapPointedComon.map f).right.hom = F.map f.right.hom := rfl

end CategoryTheory.Functor

end
