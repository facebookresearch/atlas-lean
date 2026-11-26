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
# Oplax monoidal transport of coaugmented comonoids

Let F : C ⥤ D be an oplax monoidal functor between monoidal categories with independent object
and morphism universes. Its comonoid functor sends the trivial comonoid on 𝟙_C to a comonoid
on F(𝟙_C). The canonical map from this object to the trivial comonoid on 𝟙_D has underlying
map η_F : F(𝟙_C) → 𝟙_D, the oplax unit comparison.

When η_F is invertible, it defines a comonoid isomorphism and hence a functor from comonoids
coaugmented by 𝟙_C to those coaugmented by 𝟙_D. A point e : 𝟙_C → A is sent to η_F⁻¹ ≫ F(e),
and a pointed morphism is sent to its F-image. Only the unit comparison is required to be
invertible; the oplax tensor comparisons retain their given direction.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory
open scoped ComonObj

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.OplaxMonoidal]

/-- Comonoid counit of the image of the monoidal unit.

For an oplax monoidal functor F : C ⥤ D, the comonoid F.mapComon(Comon.trivial C) has a
canonical comonoid morphism to Comon.trivial D. Its underlying arrow is the counit of the
image comonoid. -/
def unitImageCounit : F.mapComon.obj (Comon.trivial C) ⟶ Comon.trivial D := default

/-- Underlying map of the image-unit comonoid counit.

For an oplax monoidal functor F, the underlying arrow F(𝟙_C) → 𝟙_D of unitImageCounit F is
precisely the oplax unit comparison η_F. -/
theorem unitImageCounit_hom :
    (unitImageCounit F).hom = OplaxMonoidal.η F := by
  change F.map (𝟙 (𝟙_ C)) ≫ OplaxMonoidal.η F = OplaxMonoidal.η F
  rw [F.map_id, Category.id_comp]

variable [IsIso (OplaxMonoidal.η F)]

/-- Comonoid isomorphism from an invertible oplax unit comparison.

If F is oplax monoidal and η_F : F(𝟙_C) → 𝟙_D is invertible, the image of the trivial comonoid
is isomorphic to the trivial comonoid of D. The forward comonoid map is the canonical
image-unit counit. -/
def unitImageComonIso : F.mapComon.obj (Comon.trivial C) ≅ Comon.trivial D := by
  let f := unitImageCounit F
  have hη : IsIso (OplaxMonoidal.η F) := inferInstance
  letI : IsIso f.hom := by
    exact (unitImageCounit_hom F).symm ▸ hη
  let e : (F.mapComon.obj (Comon.trivial C)).X ≅ (Comon.trivial D).X := asIso f.hom
  exact Comon.mkIso e f.isComonHom_hom.hom_counit f.isComonHom_hom.hom_comul

/-- Forward arrow of the image-unit comonoid isomorphism.

For an oplax monoidal F with invertible unit comparison η_F, the underlying hom of
unitImageComonIso F is η_F : F(𝟙_C) → 𝟙_D. -/
theorem unitImageComonIso_hom_hom :
    (unitImageComonIso F).hom.hom = OplaxMonoidal.η F := unitImageCounit_hom F

/-- Inverse arrow of the image-unit comonoid isomorphism.

For an oplax monoidal F with invertible unit comparison η_F, the underlying inverse of
unitImageComonIso F is η_F⁻¹ : 𝟙_D → F(𝟙_C). -/
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

/-- Functor transporting coaugmented comonoids by an oplax monoidal functor.

Let F : C ⥤ D be oplax monoidal with invertible unit comparison. Apply its comonoid functor to
an object of Under(Comon.trivial C), then precompose its point with the inverse image-unit
comonoid isomorphism. This gives a functor to Under(Comon.trivial D). -/
def mapPointedComon : Under (Comon.trivial C) ⥤ Under (Comon.trivial D) :=
  Under.post F.mapComon ⋙ Under.map (unitImageComonIso F).inv

/-- Point of an oplax-transported comonoid.

For a coaugmented comonoid A with point e : 𝟙_C → A and an oplax monoidal F with invertible
unit comparison, the transported point is η_F⁻¹ ≫ F(e) : 𝟙_D → F(A). -/
theorem mapPointedComon_obj_point (A : Under (Comon.trivial C)) :
    (F.mapPointedComon.obj A).hom.hom = CategoryTheory.inv (OplaxMonoidal.η F) ≫
      F.map A.hom.hom := by
  change (unitImageComonIso F).inv.hom ≫ F.map A.hom.hom = _
  rw [unitImageComonIso_inv_hom]
  rfl

/-- Underlying map of an oplax-transported pointed morphism.

For a morphism f between coaugmented comonoids and an oplax monoidal F with invertible unit
comparison, the underlying comonoid map of mapPointedComon F applied to f is F applied to f's
underlying comonoid map. -/
theorem mapPointedComon_map_hom {A B : Under (Comon.trivial C)} (f : A ⟶ B) :
    (F.mapPointedComon.map f).right.hom = F.map f.right.hom := rfl

end CategoryTheory.Functor

end
