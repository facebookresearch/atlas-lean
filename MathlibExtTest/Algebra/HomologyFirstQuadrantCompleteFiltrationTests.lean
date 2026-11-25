/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltration

/-! # Tests for the complete first-quadrant filtration -/

@[expose] public section

open CategoryTheory Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantCompleteFiltrationTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example : CategoryTheory.Filtration
    (K.total (ComplexShape.down ℕ)) EInt :=
  horizontalCompleteTotalFiltration K

example (i : EInt) :
    Mono (horizontalCompleteFilteredTotalToTotal K i) :=
  inferInstance

example : horizontalCompleteFilteredTotalComplex K ⊤ =
    K.total (ComplexShape.down ℕ) :=
  rfl

example : horizontalCompleteFilteredTotalComplex K ⊥ =
    (HomologicalComplex.zero : ChainComplex C ℕ) :=
  rfl

example (a : ℤ) (ha : 0 ≤ a) :
    horizontalCompleteFilteredTotalComplex K (a : EInt) =
      horizontalFilteredTotalComplex K a.toNat :=
  horizontalCompleteFilteredTotalComplex_coe_of_nonneg K a ha

example (a : ℤ) (ha : a < 0) :
    horizontalCompleteFilteredTotalComplex K (a : EInt) =
      (HomologicalComplex.zero : ChainComplex C ℕ) :=
  horizontalCompleteFilteredTotalComplex_coe_of_neg K a ha

example (a : ℤ) (ha : 0 ≤ a) (n : ℕ) (h : n ≤ a.toNat) :
    (horizontalCompleteFilteredTotalComplex K (a : EInt)).X n ≅
      (K.total (ComplexShape.down ℕ)).X n :=
  horizontalCompleteFilteredTotalEvalIsoOfLE K a ha n h

example : CategoryTheory.Triangulated.SpectralObject
    (HomotopyCategory C (ComplexShape.up ℤ)) EInt :=
  horizontalCompleteFiltrationTriangulatedSpectralObject K

end HomologicalComplex₂.FirstQuadrantCompleteFiltrationTests

namespace HomologicalComplex₂.FirstQuadrantCompleteFiltrationTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example : CategoryTheory.Abelian.SpectralObject C EInt :=
  horizontalCompleteFiltrationSpectralObject K

end HomologicalComplex₂.FirstQuadrantCompleteFiltrationTests

end
