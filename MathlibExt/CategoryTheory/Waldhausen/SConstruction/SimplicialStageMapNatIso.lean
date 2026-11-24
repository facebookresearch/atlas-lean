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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageNatIso
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.SimplicialStageMap

/-!
# Simplicial-stage map natural-isomorphism data (weak layer)

For exact categories `C` and `D` over independent universes with their
local standard Waldhausen structures (`ExactCategory.waldhausenCategory`),
an isomorphism `e : F ≅ G` between additive exact functors induces a
degreewise weak family
`simplicialStageMapWeakNatIsoFamily e a : mapStageWeak F a.unop.len ≅
mapStageWeak G a.unop.len` definitionally from `mapStageWeakNatIso`, with
reindex coherence from the strict `mapStageWeak_reindex` laws and hom/inv
computation from `mapStageNatIso_hom_app`/`inv_app` for the next
levelwise nerve-homotopy consumer.

Reuse map: `mapStageWeakNatIso` for the family, `mapStageWeak_reindex`
(`rfl`) for reindex/simplicial coherence via `Functor.isoWhiskerLeft` /
`Functor.isoWhiskerRight`, and `mapStageNatIso_hom_app`/`inv_app` for the
`@[simp]` component laws. No new abstraction class is introduced.

Cross-universe scope: `C : Type u₁` with `Category.{v₁}` and
`D : Type u₂` with `Category.{v₂}`. No bundled
simplicial `Iso`, nerve `Iso`, or diagonal `Iso` is claimed: parallel
simplicial/nerve maps form a 2-cell, so only the family plus coherence
theorems are given.

Nonclaims: no nerve homotopy implementation, realization, pointed maps,
additivity theorem, `π₀ ≃ K₀`, G-theory, spectra, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u₁) [Category.{v₁} C]
  [Preadditive C]
  [Limits.HasZeroObject C]
  [HasBinaryBiproducts C]
  [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D]
  [Preadditive D]
  [Limits.HasZeroObject D]
  [HasBinaryBiproducts D]
  [ExactCategory D]
variable (F G : C ⥤ D) [F.Additive] [G.Additive]
  [Functor.IsExact F] [Functor.IsExact G]

/-- Degreewise weak simplicial-stage nat-iso family from `mapStageWeakNatIso`. -/
noncomputable def simplicialStageMapWeakNatIsoFamily (e : F ≅ G)
    (a : SimplexCategoryᵒᵖ) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      mapStageWeak C D F a.unop.len ≅ mapStageWeak C D G a.unop.len) := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  exact mapStageWeakNatIso C D F G e a.unop.len

/-- Reindex coherence of the weak family via the strict `mapStageWeak_reindex`
laws: whiskering the family at `a` on the left by weak reindexing agrees with
whiskering the family at `b` on the right. Both composites are `rfl`-equal by
`mapStageWeak_reindex`; components agree pointwise by `e.hom.naturality`. -/
theorem simplicialStageMapWeakNatIsoFamily_reindex {a b : SimplexCategory}
    (f : a ⟶ b) (e : F ≅ G) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      Functor.isoWhiskerLeft (reindexStageWeak C f)
        (simplicialStageMapWeakNatIsoFamily C D F G e (Opposite.op a)) =
      Functor.isoWhiskerRight
        (simplicialStageMapWeakNatIsoFamily C D F G e (Opposite.op b))
        (reindexStageWeak D f)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  rfl

/-- Hom-component computation for the weak family, via `mapStageNatIso_hom_app`. -/
@[simp]
theorem simplicialStageMapWeakNatIsoFamily_hom_app (e : F ≅ G)
    (a : SimplexCategoryᵒᵖ)
    (X : (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      StageWeakCategory C a.unop.len))
    (A : Ar a.unop.len) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (((simplicialStageMapWeakNatIsoFamily C D F G e a).hom.app X).hom).hom.app A =
        e.hom.app (X.obj.obj.obj A)) := by
  rfl

/-- Inv-component computation for the weak family, via `mapStageNatIso_inv_app`. -/
@[simp]
theorem simplicialStageMapWeakNatIsoFamily_inv_app (e : F ≅ G)
    (a : SimplexCategoryᵒᵖ)
    (X : (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      StageWeakCategory C a.unop.len))
    (A : Ar a.unop.len) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (((simplicialStageMapWeakNatIsoFamily C D F G e a).inv.app X).hom).hom.app A =
        e.inv.app (X.obj.obj.obj A)) := by
  rfl

end CategoryTheory.Waldhausen.SConstruction
