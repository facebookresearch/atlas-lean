/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationNaturality

/-! # Tests for complete-filtration naturality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantCompleteFiltrationNaturalityTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalCompleteFilteredTotalComplexMapOfBicomplexData
#check horizontalCompleteFilteredTotalComplexMapOfBicomplex
#check horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal
#check horizontalCompleteFilteredTotalComplexMapOfBicomplex_naturality
#check horizontalCompleteTotalFilteredObject
#check horizontalCompleteTotalFilteredObjectMap
#check horizontalCompleteTotalFilteredObjectMap_hom
#check horizontalCompleteTotalFilteredObjectMap_natTrans_app

example (f : K ⟶ L) (i : EInt) :
    horizontalCompleteFilteredTotalComplex K i ⟶
      horizontalCompleteFilteredTotalComplex L i :=
  horizontalCompleteFilteredTotalComplexMapOfBicomplex f i

example (f : K ⟶ L) {i j : EInt} (h : i ≤ j) :
    horizontalCompleteFilteredTotalComplexMapOfBicomplex f i ≫
        horizontalCompleteFilteredTotalMap L h =
      horizontalCompleteFilteredTotalMap K h ≫
        horizontalCompleteFilteredTotalComplexMapOfBicomplex f j :=
  horizontalCompleteFilteredTotalComplexMapOfBicomplex_naturality f h

example (f : K ⟶ L) (j : EInt) :
    horizontalCompleteFilteredTotalComplexMapOfBicomplex f ⊥ ≫
        horizontalCompleteFilteredTotalMap L (bot_le : (⊥ : EInt) ≤ j) =
      horizontalCompleteFilteredTotalMap K bot_le ≫
        horizontalCompleteFilteredTotalComplexMapOfBicomplex f j :=
  horizontalCompleteFilteredTotalComplexMapOfBicomplex_naturality
    f bot_le

example (f : K ⟶ L) :
    horizontalCompleteFilteredTotalComplexMapOfBicomplex f
          ((-1 : ℤ) : EInt) ≫
        horizontalCompleteFilteredTotalMap L (by norm_num :
          ((-1 : ℤ) : EInt) ≤ ((0 : ℤ) : EInt)) =
      horizontalCompleteFilteredTotalMap K (by norm_num) ≫
        horizontalCompleteFilteredTotalComplexMapOfBicomplex f
          ((0 : ℤ) : EInt) :=
  horizontalCompleteFilteredTotalComplexMapOfBicomplex_naturality
    f (by norm_num)

example (f : K ⟶ L) :
    horizontalCompleteFilteredTotalComplexMapOfBicomplex f
          ((0 : ℤ) : EInt) ≫
        horizontalCompleteFilteredTotalMap L le_top =
      horizontalCompleteFilteredTotalMap K le_top ≫
        horizontalCompleteFilteredTotalComplexMapOfBicomplex f ⊤ :=
  horizontalCompleteFilteredTotalComplexMapOfBicomplex_naturality
    f le_top

example (f : K ⟶ L) :
    horizontalCompleteFilteredTotalComplexMapOfBicomplex f ⊤ ≫
        horizontalCompleteFilteredTotalMap L (le_refl (⊤ : EInt)) =
      horizontalCompleteFilteredTotalMap K (le_refl (⊤ : EInt)) ≫
        horizontalCompleteFilteredTotalComplexMapOfBicomplex f ⊤ :=
  horizontalCompleteFilteredTotalComplexMapOfBicomplex_naturality
    f (le_refl (⊤ : EInt))

example (f : K ⟶ L) :
    horizontalCompleteTotalFilteredObject K ⟶
      horizontalCompleteTotalFilteredObject L :=
  horizontalCompleteTotalFilteredObjectMap f

#print axioms horizontalCompleteFilteredTotalComplexMapOfBicomplex
#print axioms horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal
#print axioms horizontalCompleteFilteredTotalComplexMapOfBicomplex_naturality
#print axioms horizontalCompleteTotalFilteredObjectMap

end HomologicalComplex₂.FirstQuadrantCompleteFiltrationNaturalityTests

end
