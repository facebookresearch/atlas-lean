/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinNaturality

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite
open scoped Simplicial
open scoped CategoryTheory.MonoidalCategory.DayFunctor

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.JoinNaturalityTest

example {X X' Y : SSet.{u}} (f : X ⟶ X') :
    SSet.Join.augDay.map ((SSet.join.map f).app Y) ≫
        (SSet.Join.augDayJoinIso X' Y).hom =
      (SSet.Join.augDayJoinIso X Y).hom ≫
        (SSet.Join.augDay.map f ▷ SSet.Join.augDay.obj Y) :=
  SSet.Join.augDayJoinIso_naturality_left f

example {X Y Y' : SSet.{u}} (g : Y ⟶ Y') :
    SSet.Join.augDay.map ((SSet.join.obj X).map g) ≫
        (SSet.Join.augDayJoinIso X Y').hom =
      (SSet.Join.augDayJoinIso X Y).hom ≫
        (SSet.Join.augDay.obj X ◁ SSet.Join.augDay.map g) :=
  SSet.Join.augDayJoinIso_naturality_right g

example (X Y : SSet.{u}) :
    SSet.Join.augDayJoinNatIso.{u}.hom.app (X, Y) =
      (SSet.Join.augDayJoinIso X Y).hom :=
  SSet.Join.augDayJoinNatIso_hom_app X Y

example {m n n' : ℕ} (φ : ⦋n⦌ ⟶ ⦋n'⦌) :
    (SSet.join.{u}.obj (Δ[m] : SSet.{u})).map (SSet.stdSimplex.map φ) ≫
        (SSet.joinStdSimplexIso.{u} m n').hom =
      (SSet.joinStdSimplexIso.{u} m n).hom ≫
        SSet.stdSimplex.map
          (AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋m⦌) φ) :=
  SSet.joinStdSimplexIso_natural_right φ

example {m n n' : ℕ} (φ : ⦋n⦌ ⟶ ⦋n'⦌) {Z : SSet.{u}}
    (h : Δ[m + n' + 1] ⟶ Z) :
    (SSet.join.{u}.obj (Δ[m] : SSet.{u})).map (SSet.stdSimplex.map φ) ≫
        (SSet.joinStdSimplexIso.{u} m n').hom ≫ h =
      (SSet.joinStdSimplexIso.{u} m n).hom ≫
        SSet.stdSimplex.map
          (AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋m⦌) φ) ≫ h :=
  SSet.joinStdSimplexIso_natural_right_assoc φ h

example (n : ℕ) :
    (λ_ (SSet.Join.augDay.{u}.obj (Δ[n] : SSet.{u}))).inv.natTrans.app
        (op (WithInitial.of ⦋n⦌)) (ULift.up (𝟙 ⦋n⦌)) =
      (DayFunctor.η (𝟙_ SSet.Join.DayCat.{u})
          (SSet.Join.augDay.{u}.obj (Δ[n] : SSet.{u}))).app
        (op WithInitial.star, op (WithInitial.of ⦋n⦌))
        (DayFunctor.ν AugmentedSimplexCategoryᵒᵖ (Type u) PUnit.unit,
          ULift.up (𝟙 ⦋n⦌)) :=
  SSet.Join.leftUnitor_inv_app_of n

example (m n : ℕ) :
    (λ_ (SSet.Join.augDay.{u}.obj (Δ[n] : SSet.{u}))).inv ≫
        (SSet.Join.dayUnitYonedaIso.{u}.hom ▷
          SSet.Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
        (SSet.Join.augDayBotIso.{u}.inv ▷
          SSet.Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
        (SSet.Join.augDay.{u}.map (initial.to (Δ[m] : SSet.{u})) ▷
          SSet.Join.augDay.{u}.obj (Δ[n] : SSet.{u})) ≫
        ((SSet.Join.augDayStdSimplexIso.{u} m).hom ⊗ₘ
          (SSet.Join.augDayStdSimplexIso.{u} n).hom) ≫
        (SSet.Join.dayTensorYonedaIso.{u} (WithInitial.of ⦋m⦌)
          (WithInitial.of ⦋n⦌)).hom =
      (SSet.Join.augDayStdSimplexIso.{u} n).hom ≫
        SSet.Join.dayYonedaMap.{u}
          (AugmentedSimplexCategory.inr (WithInitial.of ⦋m⦌)
            (WithInitial.of ⦋n⦌)) :=
  SSet.Join.joinInrDay_eq m n

example (m n : ℕ) :
    SSet.joinInr (Δ[m] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
        (SSet.joinStdSimplexIso.{u} m n).hom =
      SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋m⦌ ⦋n⦌) :=
  SSet.joinInr_comp_joinStdSimplexIso_hom m n

end MathlibExtTest.AlgebraicTopology.SimplicialSet.JoinNaturalityTest
