/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.NerveHomotopy
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat
meta import Mathlib.Tactic.Ring
meta import Mathlib.Tactic.NormNum

/-!
# Nerve cylinders and prisms with noncommuting affine maps

The walking arrow has edge `0 → 1`. Three functors send that edge to
multiplication by `2`, `3`, and `5` on rational numbers. Their transformations
have components `x+1`, `3*x/2+3`, and `2*x+1`, `10*x/3+5`.
The mixed cylinder edge sends `1` to `6`, while reversing its factors gives `4`.
The three composition-prism faces give `15`, `25`, and `6` at that coordinate.

The raw classifiers have different source/target object and morphism universes.
Native hom lifts supply the common morphism universe for the larger-target
prism. Native `AsSmall` transport also exercises the ordinary nerve homotopy
and finite-prism APIs. All lifts are actual functors, with no world assumptions.
-/

open CategoryTheory Opposite MonoidalCategory
open scoped CategoryTheory CategoryTheory.Prod Simplicial

noncomputable section

namespace MathlibExtTest.CategoryTheory.NerveHomotopy

private abbrev F₀ : ComposableArrows (Type 0) 1 :=
  ComposableArrows.mk₁ (↾fun x : ℚ => 2 * x)

private abbrev G₀ : ComposableArrows (Type 0) 1 :=
  ComposableArrows.mk₁ (↾fun x : ℚ => 3 * x)

private abbrev H₀ : ComposableArrows (Type 0) 1 :=
  ComposableArrows.mk₁ (↾fun x : ℚ => 5 * x)

private def α₀ : F₀ ⟶ G₀ :=
  ComposableArrows.homMk₁ (↾fun x : ℚ => x + 1)
    (↾fun x : ℚ => (3 / 2 : ℚ) * x + 3) (by
      change (↾fun x : ℚ => (3 / 2 : ℚ) * (2 * x) + 3) =
        (↾fun x : ℚ => 3 * (x + 1))
      ext x
      ring)

private def β₀ : G₀ ⟶ H₀ :=
  ComposableArrows.homMk₁ (↾fun x : ℚ => 2 * x + 1)
    (↾fun x : ℚ => (10 / 3 : ℚ) * x + 5) (by
      change (↾fun x : ℚ => (10 / 3 : ℚ) * (3 * x) + 5) =
        (↾fun x : ℚ => 5 * (2 * x + 1))
      ext x
      ring)

private abbrev D := ULiftHom.{1} (Type 0)
private abbrev targetUp : Type 0 ⥤ D := ULiftHom.up
private abbrev F : Fin 2 ⥤ D := F₀ ⋙ targetUp
private abbrev G : Fin 2 ⥤ D := G₀ ⋙ targetUp
private abbrev H : Fin 2 ⥤ D := H₀ ⋙ targetUp
private abbrev α : F ⟶ G := Functor.whiskerRight α₀ targetUp
private abbrev β : G ⟶ H := Functor.whiskerRight β₀ targetUp

private def f : (0 : Fin 2) ⟶ (1 : Fin 2) := homOfLE (by decide)

-- Source objects/morphisms have universe 0; target objects/morphisms have universe 1.
example : Fin 2 × Fin 3 ⥤ D := NatTrans.nerveChainFunctor α β

example : ((NatTrans.nerveCylinderFunctor α).map
    (f ×ₘ homOfLE (show (0 : Fin 2) ≤ 1 by decide))).down (1 : ℚ) = (6 : ℚ) := by
  rw [NatTrans.nerveCylinderFunctor_map_zero_one]
  change (3 : ℚ) * ((1 : ℚ) + 1) = 6
  norm_num

example : ((G.map f) ≫ α.app 0).down (1 : ℚ) = (4 : ℚ) := by
  change (3 : ℚ) * (1 : ℚ) + 1 = 4
  norm_num

example : ((NatTrans.nerveChainFunctor α β).map
    (f ×ₘ homOfLE (show (0 : Fin 3) ≤ 1 by decide))).down (1 : ℚ) = (6 : ℚ) := by
  change (3 : ℚ) * ((1 : ℚ) + 1) = 6
  norm_num

example : ((NatTrans.nerveChainFunctor α β).map
    (f ×ₘ homOfLE (show (1 : Fin 3) ≤ 2 by decide))).down (1 : ℚ) = (15 : ℚ) := by
  change (5 : ℚ) * (2 * (1 : ℚ) + 1) = 15
  norm_num

example : ((NatTrans.nerveChainFunctor α β).map
    (f ×ₘ homOfLE (show (0 : Fin 3) ≤ 2 by decide))).down (1 : ℚ) = (25 : ℚ) := by
  change (5 : ℚ) * (2 * ((1 : ℚ) + 1) + 1) = 25
  norm_num

example : ((𝟭 (Fin 2)).prod (SimplexCategory.δ (1 : Fin 3)).toOrderHom.toFunctor) ⋙
    NatTrans.nerveChainFunctor α β = NatTrans.nerveCylinderFunctor (α ≫ β) :=
  NatTrans.prod_δ_one_comp_nerveChainFunctor α β

private abbrev C := ULiftHom.{1} (Fin 2)
private abbrev sourceUp : Fin 2 ⥤ C := ULiftHom.up
private abbrev sourceDown : C ⥤ Fin 2 := ULiftHom.down
private abbrev c₀ : C := sourceUp.obj 0
private abbrev c₁ : C := sourceUp.obj 1
private abbrev f' : c₀ ⟶ c₁ := sourceUp.map f
private abbrev F' : C ⥤ D := sourceDown ⋙ F
private abbrev G' : C ⥤ D := sourceDown ⋙ G
private abbrev H' : C ⥤ D := sourceDown ⋙ H
private abbrev α' : F' ⟶ G' := Functor.whiskerLeft sourceDown α
private abbrev β' : G' ⟶ H' := Functor.whiskerLeft sourceDown β

private abbrev d : SimplexCategoryᵒᵖ := op (SimplexCategory.mk 1)
private abbrev edge : (nerve C).obj d := ComposableArrows.mk₁ f'
private abbrev interval : (Δ[1] : SSet.{1}).obj d :=
  SSet.stdSimplex.objEquiv.{1}.symm (𝟙 (SimplexCategory.mk 1))
private abbrev mixed : (nerve C ⊗ (Δ[1] : SSet.{1})).obj d := (edge, interval)

example : SSet.stdSimplex.asOrderHom interval 0 = 0 ∧
    SSet.stdSimplex.asOrderHom interval 1 = 1 := ⟨rfl, rfl⟩

private abbrev cylinder := NatTrans.nerveHomotopyMapCommonHomUp.{0, 1, 0} α'

/-- The actual cylinder simplex has the expected mixed-edge chain. -/
private lemma mixed_chain : cylinder.app d mixed =
    ComposableArrows.mk₁ (α'.app c₀ ≫ G'.map f') := by
  let X : ComposableArrows D 1 := cylinder.app d mixed
  have hx : X.hom = α'.app c₀ ≫ G'.map f' := by
    change (NatTrans.nerveCylinderFunctor α').map
      (f' ×ₘ homOfLE (show (0 : Fin 2) ≤ 1 by decide)) = α'.app c₀ ≫ G'.map f'
    exact NatTrans.nerveCylinderFunctor_map_zero_one α' f'
  exact (ComposableArrows.mk₁_hom X).symm.trans (congrArg ComposableArrows.mk₁ hx)

example : ((cylinder.app d mixed).map f).down (1 : ℚ) = (6 : ℚ) := by
  change (3 : ℚ) * ((1 : ℚ) + 1) = 6
  norm_num

private abbrev prism := NatTrans.nerveCompositionPrismMapCommonHomUp.{0, 1, 0} α' β'

example : (nerve C ◁ SSet.stdSimplex.δ (0 : Fin 3)) ≫ prism =
    NatTrans.nerveHomotopyMapCommonHomUp.{0, 1, 0} β' :=
  NatTrans.nerveCompositionPrismMapCommonHomUp_face_zero α' β'

example : (nerve C ◁ SSet.stdSimplex.δ (1 : Fin 3)) ≫ prism =
    NatTrans.nerveHomotopyMapCommonHomUp.{0, 1, 0} (α' ≫ β') :=
  NatTrans.nerveCompositionPrismMapCommonHomUp_face_one α' β'

example : (nerve C ◁ SSet.stdSimplex.δ (2 : Fin 3)) ≫ prism =
    NatTrans.nerveHomotopyMapCommonHomUp.{0, 1, 0} α' :=
  NatTrans.nerveCompositionPrismMapCommonHomUp_face_two α' β'

example : ((prism.app d ((nerve C ◁ SSet.stdSimplex.δ (1 : Fin 3)).app d mixed)).map f).down
    (1 : ℚ) = (25 : ℚ) := by
  change (5 : ℚ) * (2 * ((1 : ℚ) + 1) + 1) = 25
  norm_num

private abbrev E := AsSmall.{1} C
private abbrev smallUp : C ⥤ E := AsSmall.up
private abbrev smallDown : E ⥤ C := AsSmall.down
private abbrev Fs : E ⥤ D := smallDown ⋙ F'
private abbrev Gs : E ⥤ D := smallDown ⋙ G'
private abbrev αs : Fs ⟶ Gs := Functor.whiskerLeft smallDown α'
private abbrev smallEdge : (nerve E).obj d := ComposableArrows.mk₁ (smallUp.map f')
private abbrev smallMixed : (nerve E ⊗ (Δ[1] : SSet.{1})).obj d := (smallEdge, interval)

example : SSet.ι₀ ≫ (NatTrans.nerveHomotopy αs).h = nerveMap Fs :=
  (NatTrans.nerveHomotopy αs).h₀

example : SSet.ι₁ ≫ (NatTrans.nerveHomotopy αs).h = nerveMap Gs :=
  (NatTrans.nerveHomotopy αs).h₁

example : (((nerveMap Fs).app d smallEdge).map f).down (1 : ℚ) = (2 : ℚ) := by
  change (2 : ℚ) * (1 : ℚ) = 2
  norm_num

example : (((nerveMap Gs).app d smallEdge).map f).down (1 : ℚ) = (3 : ℚ) := by
  change (3 : ℚ) * (1 : ℚ) = 3
  norm_num

example : (NatTrans.nerveHomotopy αs).h = NatTrans.nerveHomotopyMap αs :=
  NatTrans.nerveHomotopy_h αs

example : (NatTrans.nerveCylinderFunctor αs).nervePrismMap =
    NatTrans.nerveHomotopyMap αs := NatTrans.nervePrismMap_nerveCylinderFunctor αs

example : ((((NatTrans.nerveCylinderFunctor αs).nervePrismMap).app d smallMixed).map f).down
    (1 : ℚ) = (6 : ℚ) := by
  change (3 : ℚ) * ((1 : ℚ) + 1) = 6
  norm_num

end MathlibExtTest.CategoryTheory.NerveHomotopy
