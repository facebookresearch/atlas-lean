/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationFiniteComparison

/-! # Tests for complete/finite filtration-stage comparison -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantCompleteFiltrationFiniteComparisonTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalCompleteFilteredTotalComplexFiniteIso
#check horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal
#check horizontalCompleteFilteredTotalComplexFiniteIso_naturality
#check horizontalCompleteFilteredTotalComplexFiniteIso_transition

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (a : ℤ) (ha : 0 ≤ a) :
    horizontalCompleteFilteredTotalComplex K (a : EInt) ≅
      horizontalFilteredTotalComplex K a.toNat :=
  horizontalCompleteFilteredTotalComplexFiniteIso K a ha

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (a : ℤ) (ha : 0 ≤ a) :
    (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        horizontalFilteredTotalComplexToTotal K a.toNat =
      horizontalCompleteFilteredTotalToTotal K (a : EInt) :=
  horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal K a ha

example (f : K ⟶ L) (a : ℤ) (ha : 0 ≤ a) :
    (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        horizontalFilteredTotalComplexMapOfBicomplex f a.toNat =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex f (a : EInt) ≫
        (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).hom :=
  horizontalCompleteFilteredTotalComplexFiniteIso_naturality f a ha

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (a b : ℤ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        horizontalFilteredTotalComplexMap K (Int.toNat_le_toNat hab) =
      horizontalCompleteFilteredTotalMap K
          (WithBotTop.coe_monotone hab) ≫
        (horizontalCompleteFilteredTotalComplexFiniteIso K b
          (ha.trans hab)).hom :=
  horizontalCompleteFilteredTotalComplexFiniteIso_transition K a b ha hab

#print axioms horizontalCompleteFilteredTotalComplexFiniteIso
#print axioms horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal
#print axioms horizontalCompleteFilteredTotalComplexFiniteIso_naturality
#print axioms horizontalCompleteFilteredTotalComplexFiniteIso_transition

end HomologicalComplex₂.FirstQuadrantCompleteFiltrationFiniteComparisonTests

end
