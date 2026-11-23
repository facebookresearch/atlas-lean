/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanVerticalCoefficientBarNaturality
public import MathlibExt.Algebra.Homology.HomologyMapSquare

/-!
# Naturality of iterated Bousfield--Kan homology

The homology of the horizontal complex of Bousfield--Kan vertical homology is
identified naturally with category homology of the pointwise homology
coefficient system.  The final comparison from the alternating coefficient
bar to the normalized bar is natural because its underlying inverse map is
the natural projection `PInftyToNormalizedMooreComplex`.

This file does not construct a morphism of spectral sequences or claim
naturality of the second page.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe v u w

namespace AlgebraicTopology.DoldKan

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The inverse homology comparison from the alternating-face complex to the
normalized Moore complex is natural in the simplicial object. -/
theorem normalizedMooreAlternatingHomologyIso_inv_naturality
    {X Y : SimplicialObject A} (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap
          ((AlgebraicTopology.alternatingFaceMapComplex A).map f) n ≫
        ((homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
          (Y := Y)).toHomologyIso n).inv =
      ((homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
          (Y := X)).toHomologyIso n).inv ≫
        HomologicalComplex.homologyMap
          ((AlgebraicTopology.normalizedMooreComplex A).map f) n := by
  change HomologicalComplex.homologyMap
        (AlternatingFaceMapComplex.map f) n ≫
      HomologicalComplex.homologyMap
        (PInftyToNormalizedMooreComplex Y) n =
    HomologicalComplex.homologyMap
        (PInftyToNormalizedMooreComplex X) n ≫
      HomologicalComplex.homologyMap
        (NormalizedMooreComplex.map f) n
  exact HomologicalComplex.homologyMap_square
    (PInftyToNormalizedMooreComplex_naturality f) n

end AlgebraicTopology.DoldKan

universe vJ

namespace SSet

variable {J : Type w} [Category.{vJ} J]

local notation "c" => ComplexShape.down ℕ

/-- Iterated vertical-then-horizontal homology of the Bousfield--Kan
bicomplex is category homology with coefficients in pointwise homology. -/
noncomputable def bkVerticalHorizontalCoefficientHomologyIso
    (R : AddCommGrpCat.{max w vJ}) (D : J ⥤ SSet.{max w vJ}) (p q : ℕ) :
    ((bkAlternatingBicomplex AddCommGrpCat.{max w vJ} R D).verticalHomologyComplex q).homology p ≅
      CategoryTheory.CategoryHomology.homologyWithCoefficients
        (D ⋙ SSet.homologyFunctor R q) p :=
  HomologicalComplex.homologyMapIso
      (bkVerticalHomologyCoefficientBarComplexIso R D q) p ≪≫
    ((AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := CategoryTheory.CategoryHomology.coefficientBarSimplicial
        (D ⋙ SSet.homologyFunctor R q))).toHomologyIso p).symm

/-- The iterated Bousfield--Kan homology comparison is natural in the
simplicial-set valued diagram. -/
theorem bkVerticalHorizontalCoefficientHomologyIso_hom_naturality
    (R : AddCommGrpCat.{max w vJ}) {D E : J ⥤ SSet.{max w vJ}}
    (α : D ⟶ E) (p q : ℕ) :
    HomologicalComplex.homologyMap
          (((HomologicalComplex.homologyFunctor AddCommGrpCat.{max w vJ} c q).mapHomologicalComplex c).map
            ((bkAlternatingBicomplexFunctor AddCommGrpCat.{max w vJ} R).map α)) p ≫
        (bkVerticalHorizontalCoefficientHomologyIso R E p q).hom =
      (bkVerticalHorizontalCoefficientHomologyIso R D p q).hom ≫
        (CategoryTheory.CategoryHomology.homologyWithCoefficientsFunctor
          (C := J) (A := AddCommGrpCat.{max w vJ}) p).map
            (Functor.whiskerRight α (SSet.homologyFunctor R q)) := by
  let β := Functor.whiskerRight α (SSet.homologyFunctor R q)
  let f := ((HomologicalComplex.homologyFunctor
    AddCommGrpCat.{max w vJ} c q).mapHomologicalComplex c).map
      ((bkAlternatingBicomplexFunctor AddCommGrpCat.{max w vJ} R).map α)
  let g := (AlgebraicTopology.alternatingFaceMapComplex
    AddCommGrpCat.{max w vJ}).map
      (CategoryTheory.CategoryHomology.coefficientBarSimplicialMap β)
  have hComplex :=
    bkVerticalHomologyCoefficientBarComplexIso_hom_naturality R α q
  have hHom := HomologicalComplex.homologyMap_square hComplex p
  have hDK :=
    AlgebraicTopology.DoldKan.normalizedMooreAlternatingHomologyIso_inv_naturality
      (CategoryTheory.CategoryHomology.coefficientBarSimplicialMap β) p
  change HomologicalComplex.homologyMap g p ≫
      HomologicalComplex.homologyMap
        (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex
          (CategoryTheory.CategoryHomology.coefficientBarSimplicial
            (E ⋙ SSet.homologyFunctor R q))) p =
    HomologicalComplex.homologyMap
        (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex
          (CategoryTheory.CategoryHomology.coefficientBarSimplicial
            (D ⋙ SSet.homologyFunctor R q))) p ≫
      HomologicalComplex.homologyMap
        ((CategoryTheory.CategoryHomology.normalizedCoefficientBarComplexFunctor
          (C := J) (A := AddCommGrpCat.{max w vJ})).map β) p at hDK
  dsimp only [bkVerticalHorizontalCoefficientHomologyIso, Iso.trans_hom,
    HomologicalComplex.homologyMapIso, HomotopyEquiv.toHomologyIso]
  change HomologicalComplex.homologyMap f p ≫
      (HomologicalComplex.homologyMap
          (bkVerticalHomologyCoefficientBarComplexIso R E q).hom p ≫
        HomologicalComplex.homologyMap
          (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex
            (CategoryTheory.CategoryHomology.coefficientBarSimplicial
              (E ⋙ SSet.homologyFunctor R q))) p) =
    (HomologicalComplex.homologyMap
        (bkVerticalHomologyCoefficientBarComplexIso R D q).hom p ≫
      HomologicalComplex.homologyMap
        (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex
          (CategoryTheory.CategoryHomology.coefficientBarSimplicial
            (D ⋙ SSet.homologyFunctor R q))) p) ≫
      HomologicalComplex.homologyMap
        ((CategoryTheory.CategoryHomology.normalizedCoefficientBarComplexFunctor
          (C := J) (A := AddCommGrpCat.{max w vJ})).map β) p
  rw [← Category.assoc, hHom]
  rw [Category.assoc, hDK]
  rfl

end SSet

end
