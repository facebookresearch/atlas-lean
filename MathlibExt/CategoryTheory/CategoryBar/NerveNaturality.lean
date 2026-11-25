/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryBar.NerveComparison
public import MathlibExt.CategoryTheory.CategoryBar.Change

/-!
# Category bar: index-naturality of the unit comparison with the nerve

For an index functor `F : C ⥤ D`, the unit-coefficient bar comparison is
naturally indexed: the simplicial square
`categoryBarIdxMap F ⋙ (barNerveUnitSimplicialIso D).hom =
 (barNerveUnitSimplicialIso C).hom ⋙ nerveMap F`
commutes, degreewise via `barNerveUnit_indexNaturality`.

Universe boundary: this API uses common object and morphism universes where
required by the pinned `nerveMap`/simplicial-set interface; this is an interface
limitation, not a mathematical restriction.

Nonclaims: no Data-level duplicate, generic coefficient-iso promotion,
comma/Grothendieck, opposite/reversal, contraction, homotopy, or KQ result.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v

namespace CategoryTheory

namespace CategoryBar

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- Left unit-coefficient map induced by an index functor. -/
def unitIdxL (F : C ⥤ D) : unitCoeffL C ⟶ F ⋙ unitCoeffL D where
  app _ := 𝟙 _
  naturality _ _ _ := rfl

/-- Right unit-coefficient map induced by an index functor. -/
def unitIdxR (F : C ⥤ D) : unitCoeffR C ⟶ F.op ⋙ unitCoeffR D where
  app _ := 𝟙 _
  naturality _ _ _ := rfl

/-- Degreewise naturality of the unit-bar comparison with the nerve. -/
theorem barNerveUnit_indexNaturality (F : C ⥤ D) {n : ℕ}
    (x : barObj C (unitCoeffR C) (unitCoeffL C) n) :
    barNerveUnitEquiv D n (barIdxMap F (unitIdxR F) (unitIdxL F) x) =
      (nerveMap F).app (Opposite.op (SimplexCategory.mk n))
        (barNerveUnitEquiv C n x) := by
  obtain ⟨Fch, l, r⟩ := x
  rfl

/-- Simplicial-set naturality of the unit-bar comparison with the nerve. -/
theorem barNerveUnitSimplicial_indexNaturality (F : C ⥤ D) :
    categoryBarIdxMap F (unitIdxR F) (unitIdxL F) ≫
        (barNerveUnitSimplicialIso D).hom =
      (barNerveUnitSimplicialIso C).hom ≫ nerveMap F := by
  ext Δ x
  obtain ⟨⟨n⟩⟩ := Δ
  exact barNerveUnit_indexNaturality F x

end CategoryBar

end CategoryTheory
