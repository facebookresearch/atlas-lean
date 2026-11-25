/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantBottomRelativeNaturality

/-! # Tests for bottom-relative bicomplex naturality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ComposableArrows

universe v u

namespace HomologicalComplex₂.FirstQuadrantBottomRelativeNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalBottomStageShortComplexMapOfBicomplex
#check horizontalBottomMappingConeToStage_naturality_of_bicomplex
#check horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex

example (f : K ⟶ L) (i : EInt) :
    (horizontalCompleteFiltrationMappingConeNatTrans f).app
          (mk₁ (horizontalBottomToStageMap i)) ≫
        horizontalBottomMappingConeToStage L i =
      horizontalBottomMappingConeToStage K i ≫
        (horizontalCompleteFiltrationCochainDiagramNatTrans f).app i :=
  horizontalBottomMappingConeToStage_naturality_of_bicomplex f i

example (f : K ⟶ L) (i : EInt) (n : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-(n : ℤ))).app (mk₁ (horizontalBottomToStageMap i)) ≫
      (horizontalBottomRelativeHomologyStageIso L i n).hom =
    (horizontalBottomRelativeHomologyStageIso K i n).hom ≫
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex f i) n :=
  horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex f i n

-- Literal bottom stage.
example (f : K ⟶ L) (n : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-(n : ℤ))).app
          (mk₁ (horizontalBottomToStageMap (⊥ : EInt))) ≫
      (horizontalBottomRelativeHomologyStageIso L (⊥ : EInt) n).hom =
    (horizontalBottomRelativeHomologyStageIso K (⊥ : EInt) n).hom ≫
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex
          f (⊥ : EInt)) n :=
  horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex
    f (⊥ : EInt) n

-- Negative stage `-1`.
example (f : K ⟶ L) (n : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-(n : ℤ))).app
          (mk₁ (horizontalBottomToStageMap ((-1 : ℤ) : EInt))) ≫
      (horizontalBottomRelativeHomologyStageIso L ((-1 : ℤ) : EInt) n).hom =
    (horizontalBottomRelativeHomologyStageIso K ((-1 : ℤ) : EInt) n).hom ≫
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex
          f ((-1 : ℤ) : EInt)) n :=
  horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex
    f ((-1 : ℤ) : EInt) n

-- Stage zero.
example (f : K ⟶ L) (n : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-(n : ℤ))).app
          (mk₁ (horizontalBottomToStageMap ((0 : ℤ) : EInt))) ≫
      (horizontalBottomRelativeHomologyStageIso L ((0 : ℤ) : EInt) n).hom =
    (horizontalBottomRelativeHomologyStageIso K ((0 : ℤ) : EInt) n).hom ≫
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex
          f ((0 : ℤ) : EInt)) n :=
  horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex
    f ((0 : ℤ) : EInt) n

-- A positive complete-filtration stage.
example (f : K ⟶ L) (n : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-(n : ℤ))).app
          (mk₁ (horizontalBottomToStageMap ((3 : ℤ) : EInt))) ≫
      (horizontalBottomRelativeHomologyStageIso L ((3 : ℤ) : EInt) n).hom =
    (horizontalBottomRelativeHomologyStageIso K ((3 : ℤ) : EInt) n).hom ≫
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex
          f ((3 : ℤ) : EInt)) n :=
  horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex
    f ((3 : ℤ) : EInt) n

-- Top complete-filtration stage.
example (f : K ⟶ L) (n : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-(n : ℤ))).app
          (mk₁ (horizontalBottomToStageMap (⊤ : EInt))) ≫
      (horizontalBottomRelativeHomologyStageIso L (⊤ : EInt) n).hom =
    (horizontalBottomRelativeHomologyStageIso K (⊤ : EInt) n).hom ≫
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex
          f (⊤ : EInt)) n :=
  horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex
    f (⊤ : EInt) n

-- Homology degree zero uses cochain degree zero exactly.
example (f : K ⟶ L) (i : EInt) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom 0).app
          (mk₁ (horizontalBottomToStageMap i)) ≫
      (horizontalBottomRelativeHomologyStageIso L i 0).hom =
    (horizontalBottomRelativeHomologyStageIso K i 0).hom ≫
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex f i) 0 :=
  horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex f i 0

-- Identity bicomplex maps are accepted at every stage and degree.
example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (i : EInt) (n : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap (𝟙 K)).hom
        (-(n : ℤ))).app (mk₁ (horizontalBottomToStageMap i)) ≫
      (horizontalBottomRelativeHomologyStageIso K i n).hom =
    (horizontalBottomRelativeHomologyStageIso K i n).hom ≫
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex (𝟙 K) i) n :=
  horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex
    (𝟙 K) i n

#print axioms horizontalBottomStageShortComplexMapOfBicomplex
#print axioms horizontalBottomMappingConeToStage_naturality_of_bicomplex
#print axioms horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex

end HomologicalComplex₂.FirstQuadrantBottomRelativeNaturalityTests

end
