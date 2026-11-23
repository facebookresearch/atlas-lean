/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanVerticalHomologyComplex
public import MathlibExt.CategoryTheory.CategoryHomology.WeightedBar
public import MathlibExt.CategoryTheory.CategoryHomology.BarFunctoriality
public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedCommaHomologyNaturality
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaHomologyBicomplex
public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedFiberHomologyBar
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-!
# Vertical homology and the fiber coefficient bar

The horizontal complex of vertical homology for the right-comma
Bousfield--Kan bicomplex is identified with the existing coefficient-bar
complex of `fiberHomologyFunctor`. Taking horizontal homology then gives
the neutral bigraded family `fiberHomologyCategoryHomology`.

This file itself remains page-neutral; `BousfieldKanSpectralSequence` uses
these isomorphisms to state the second page and bounded convergence theorem.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped Simplicial

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v

namespace SSet

variable {J : Type w} [Category.{v} J]

/-- The BK vertical-homology complex is the coefficient-bar complex of the
pointwise homology diagram. -/
noncomputable def bkVerticalHomologyCoefficientBarComplexIso
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v}) (q : ℕ) :
    (bkAlternatingBicomplex
      AddCommGrpCat.{max w v} R D).verticalHomologyComplex q ≅
      CategoryTheory.CategoryHomology.coefficientBarComplex
        (D ⋙ SSet.homologyFunctor R q) :=
  bkVerticalHomologyComplexIso R D q ≪≫
    CategoryTheory.CategoryHomology.terminalWeightCoefficientBarComplexIso
      (D ⋙ SSet.homologyFunctor R q)

end SSet

namespace CategoryTheory.Functor.IsCofibered

variable {S X : Type (max w v)} [Category.{v} S] [Category.{v} X]
  {p : X ⥤ S} [p.IsCofibered]

/-- The natural comma/fiber homology isomorphism induces an isomorphism of
alternating coefficient-bar complexes. -/
noncomputable def commaFiberCoefficientBarComplexIso
    (R : AddCommGrpCat.{max w v}) (q : ℕ) :
    CategoryHomology.coefficientBarComplex
        (costructuredHomologyFunctor (p := p) AddCommGrpCat.{max w v} R q) ≅
      CategoryHomology.coefficientBarComplex
        (fiberHomologyFunctor (p := p) AddCommGrpCat.{max w v} R q) :=
  (AlgebraicTopology.alternatingFaceMapComplex
    AddCommGrpCat.{max w v}).mapIso
      ((CategoryHomology.coefficientBarSimplicialFunctor
        (C := S) (A := AddCommGrpCat.{max w v})).mapIso
          (costructuredFiberHomologyNatIso
            (p := p) AddCommGrpCat.{max w v} R q))

/-- For a cofibered functor, vertical homology of the right-comma BK
bicomplex is the coefficient-bar complex of strict-fiber homology. -/
noncomputable def cofiberedVerticalHomologyComplexIso
    (R : AddCommGrpCat.{max w v}) (q : ℕ) :
    (SSet.bkAlternatingBicomplex AddCommGrpCat.{max w v} R
      (SSet.rightCommaNerveDiagram p)).verticalHomologyComplex q ≅
      CategoryHomology.coefficientBarComplex
        (fiberHomologyFunctor (p := p) AddCommGrpCat.{max w v} R q) :=
  SSet.bkVerticalHomologyCoefficientBarComplexIso R
      (SSet.rightCommaNerveDiagram p) q ≪≫
    commaFiberCoefficientBarComplexIso (p := p) R q

/-- Iterated vertical-then-horizontal homology of the right-comma BK
bicomplex is the already-defined category homology with fiber-homology
coefficients. -/
noncomputable def cofiberedVerticalHorizontalHomologyIso
    (R : AddCommGrpCat.{max w v}) (pDegree qDegree : ℕ) :
    ((SSet.bkAlternatingBicomplex AddCommGrpCat.{max w v} R
      (SSet.rightCommaNerveDiagram p)).verticalHomologyComplex qDegree).homology
        pDegree ≅
      fiberHomologyCategoryHomology (p := p) AddCommGrpCat.{max w v} R
        pDegree qDegree :=
  HomologicalComplex.homologyMapIso
      (cofiberedVerticalHomologyComplexIso (p := p) R qDegree) pDegree ≪≫
    ((AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := CategoryHomology.coefficientBarSimplicial
        (fiberHomologyFunctor (p := p) AddCommGrpCat.{max w v} R qDegree))).toHomologyIso
          pDegree).symm

end CategoryTheory.Functor.IsCofibered

end
