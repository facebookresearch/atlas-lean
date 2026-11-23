/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationFilteredHomotopy

public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ZeroObject
open HomologicalComplex₂

namespace CategoryTheory.SInverseS

local instance : HasCoproducts.{0} AddCommGrpCat.{0} := by
  let h : HasColimitsOfSize.{0, 0} AddCommGrpCat.{0} := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

variable {C : Type} [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  (R : AddCommGrpCat)

local notation "D" => SSet.rightCommaNerveDiagram (translationProjection (C := C))
local notation "K" => SSet.bkAlternatingBicomplex AddCommGrpCat R D

-- The public unit law has the literal identity stage map as endpoint.
example (i : EInt) :
    _root_.Homotopy (secondTranslationBKCompleteMap R (0 : C) i)
      (𝟙 (horizontalCompleteFilteredTotalComplex K i)) :=
  secondTranslationBKCompleteZeroHomotopy R i

-- The public multiplication law has the prescribed order of actual maps.
example (A B : C) (i : EInt) :
    _root_.Homotopy (secondTranslationBKCompleteMap R (A ⊞ B) i)
      (secondTranslationBKCompleteMap R B i ≫ secondTranslationBKCompleteMap R A i) :=
  secondTranslationBKCompleteBiprodHomotopy R A B i

-- The source-bound scalar homotopy retains the actual total coordinate.
example {A B : C} (e : A ≅ B) (i : EInt) (n m : ℕ) :
    (secondTranslationBKCompleteScalarHomotopy R e i).hom n m ≫
        (horizontalCompleteFilteredTotalToTotal K i).f m =
      (horizontalCompleteFilteredTotalToTotal K i).f n ≫
        (secondTranslationBKTotalScalarHomotopy R e).hom n m :=
  secondTranslationBKCompleteScalarHomotopy_toTotal R e i n m

-- Complete transitions may include bottom, negatives and top; no stage bound is assumed.
example (A B : C) {i j : EInt} (hij : i ≤ j) (n m : ℕ) :
    (horizontalCompleteFilteredTotalMap K hij).f n ≫
        (secondTranslationBKCompleteBiprodHomotopy R A B j).hom n m =
      (secondTranslationBKCompleteBiprodHomotopy R A B i).hom n m ≫
        (horizontalCompleteFilteredTotalMap K hij).f m :=
  secondTranslationBKCompleteBiprodHomotopy_naturality R A B hij n m

-- The finite-stage unit law also has a literal identity endpoint.
example (k : ℕ) :
    _root_.Homotopy (secondTranslationBKFiniteMap R (0 : C) k)
      (𝟙 (horizontalFilteredTotalComplex K k)) :=
  secondTranslationBKFiniteZeroHomotopy R k

-- Every interval uses the already chosen spectral-object cone functor.
example {A B : C} (e : A ≅ B) (I : ComposableArrows EInt 1) :
    _root_.Homotopy (secondTranslationBKIntervalMap R A I)
      (secondTranslationBKIntervalMap R B I) :=
  secondTranslationBKIntervalScalarHomotopy R e I

example (I : ComposableArrows EInt 1) :
    _root_.Homotopy (secondTranslationBKIntervalMap R (0 : C) I)
      (𝟙 ((horizontalCompleteFiltrationMappingConeFunctor K).obj I)) :=
  secondTranslationBKIntervalZeroHomotopy R I

example (A B : C) (I : ComposableArrows EInt 1) :
    _root_.Homotopy (secondTranslationBKIntervalMap R (A ⊞ B) I)
      (secondTranslationBKIntervalMap R B I ≫ secondTranslationBKIntervalMap R A I) :=
  secondTranslationBKIntervalBiprodHomotopy R A B I

#print axioms CategoryTheory.SInverseS.secondTranslationDiagramScalarHomotopy
#print axioms CategoryTheory.SInverseS.secondTranslationDiagramZeroHomotopy
#print axioms CategoryTheory.SInverseS.secondTranslationDiagramBiprodHomotopy
#print axioms CategoryTheory.SInverseS.secondTranslationBKTotalScalarHomotopy
#print axioms CategoryTheory.SInverseS.secondTranslationBKTotalZeroHomotopy
#print axioms CategoryTheory.SInverseS.secondTranslationBKTotalBiprodHomotopy
#print axioms CategoryTheory.SInverseS.secondTranslationBKCompleteScalarHomotopy
#print axioms CategoryTheory.SInverseS.secondTranslationBKCompleteZeroHomotopy
#print axioms CategoryTheory.SInverseS.secondTranslationBKCompleteBiprodHomotopy
#print axioms CategoryTheory.SInverseS.secondTranslationBKIntervalScalarHomotopy
#print axioms CategoryTheory.SInverseS.secondTranslationBKIntervalZeroHomotopy
#print axioms CategoryTheory.SInverseS.secondTranslationBKIntervalBiprodHomotopy

end CategoryTheory.SInverseS
