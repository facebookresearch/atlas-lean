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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.SimplicialStageMapNatIso

/-!
# Simplicial stage-map natural-isomorphism consumer tests

Focused cross-universe checks for `simplicialStageMapWeakNatIsoFamily` at a
reflexive functor iso: the degreewise family type, hom/inv component
computation, and reindex coherence. No `Iso` between parallel simplicial or
nerve maps is claimed.

Nonclaims: no nerve homotopy, realization, pointed maps, additivity, `π₀ ≃ K₀`,
G-theory, spectra, or Q/S comparison.
-/

open CategoryTheory Limits Opposite
open CategoryTheory.Waldhausen.SConstruction

universe v₁ u₁ v₂ u₂

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.SimplicialStageMapNatIsoTests

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Limits.HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D] [Preadditive D] [Limits.HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

local instance : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D

/-- Degreewise family at `Iso.refl F` is an endo-iso on `mapStageWeak`.

Protects against a family regression that changes the degreewise type. -/
noncomputable example (a : SimplexCategoryᵒᵖ) :
    mapStageWeak C D F a.unop.len ≅ mapStageWeak C D F a.unop.len :=
  simplicialStageMapWeakNatIsoFamily C D F F (Iso.refl F) a

/-- Hom-component computation at `Iso.refl F` agrees with `e.hom`.

Protects against a component regression that breaks the hom projection. -/
example (a : SimplexCategoryᵒᵖ)
    (X : StageWeakCategory C a.unop.len)
    (A : Ar a.unop.len) :
    (((simplicialStageMapWeakNatIsoFamily C D F F (Iso.refl F) a).hom.app X).hom).hom.app A =
      (Iso.refl F).hom.app (X.obj.obj.obj A) :=
  simplicialStageMapWeakNatIsoFamily_hom_app C D F F (Iso.refl F) a X A

/-- Inv-component computation at `Iso.refl F` agrees with `e.inv`.

Protects against a component regression that breaks the inv projection. -/
example (a : SimplexCategoryᵒᵖ)
    (X : StageWeakCategory C a.unop.len)
    (A : Ar a.unop.len) :
    (((simplicialStageMapWeakNatIsoFamily C D F F (Iso.refl F) a).inv.app X).hom).hom.app A =
      (Iso.refl F).inv.app (X.obj.obj.obj A) :=
  simplicialStageMapWeakNatIsoFamily_inv_app C D F F (Iso.refl F) a X A

/-- Reindex coherence at `Iso.refl F`: left-whiskered family at `a` agrees with
right-whiskered family at `b`.

Protects against an orientation slip that whiskers the wrong leg. -/
example {a b : SimplexCategory} (f : a ⟶ b) :
    Functor.isoWhiskerLeft (reindexStageWeak C f)
      (simplicialStageMapWeakNatIsoFamily C D F F (Iso.refl F) (Opposite.op a)) =
    Functor.isoWhiskerRight
      (simplicialStageMapWeakNatIsoFamily C D F F (Iso.refl F) (Opposite.op b))
      (reindexStageWeak D f) :=
  simplicialStageMapWeakNatIsoFamily_reindex C D F F f (Iso.refl F)

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.SimplicialStageMapNatIsoTests
