/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Monoidal structure on `ObjectProperty.lift`

For `P : ObjectProperty D` with `P.IsMonoidal`, `P.FullSubcategory` is monoidal.
If `F : C ⥤ D` is strong monoidal and `hF : ∀ X, P (F.obj X)`, then the lifted functor
`P.lift F hF : C ⥤ P.FullSubcategory` needs a `Monoidal` instance; we construct it from
`F`'s structure isos via `P.isoMk` and check coherence via `P.hom_ext`, so that
`P.ι` maps its `ε`/`μ`/`η`/`δ` to those of `F`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace ObjectProperty

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable (P : ObjectProperty D) [P.IsMonoidal]
variable {F : C ⥤ D} [F.Monoidal]
variable (hF : ∀ X : C, P (F.obj X))

/-- The lifted functor `P.lift F hF` is strong monoidal when `P` is monoidal and
`F` is strong monoidal. -/
instance liftMonoidal : (P.lift F hF).Monoidal :=
  let core : (P.lift F hF).CoreMonoidal :=
    { εIso := P.isoMk (Functor.Monoidal.εIso F)
      μIso := fun X Y => P.isoMk (Functor.Monoidal.μIso F X Y)
      μIso_hom_natural_left := fun {X Y} f X' => by
        apply hom_ext
        exact Functor.LaxMonoidal.μ_natural_left (F := F) f X'
      μIso_hom_natural_right := fun {X Y} X' f => by
        apply hom_ext
        exact Functor.LaxMonoidal.μ_natural_right (F := F) X' f
      associativity := fun X Y Z => by
        apply hom_ext
        exact Functor.LaxMonoidal.associativity (F := F) X Y Z
      left_unitality := fun X => by
        apply hom_ext
        exact Functor.LaxMonoidal.left_unitality (F := F) X
      right_unitality := fun X => by
        apply hom_ext
        exact Functor.LaxMonoidal.right_unitality (F := F) X }
  core.toMonoidal

@[simp]
lemma ι_map_lift_ε :
    P.ι.map (Functor.LaxMonoidal.ε (P.lift F hF)) = Functor.LaxMonoidal.ε F :=
  rfl

@[simp]
lemma ι_map_lift_η :
    P.ι.map (Functor.OplaxMonoidal.η (P.lift F hF)) = Functor.OplaxMonoidal.η F :=
  rfl

@[simp]
lemma ι_map_lift_μ (X Y : C) :
    P.ι.map (Functor.LaxMonoidal.μ (P.lift F hF) X Y) =
      Functor.LaxMonoidal.μ F X Y :=
  rfl

@[simp]
lemma ι_map_lift_δ (X Y : C) :
    P.ι.map (Functor.OplaxMonoidal.δ (P.lift F hF) X Y) =
      Functor.OplaxMonoidal.δ F X Y :=
  rfl

end ObjectProperty
end CategoryTheory
