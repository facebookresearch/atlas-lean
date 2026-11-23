/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationSpectralHomotopy
import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationFilteredHomotopy

/-!
# The actual second-translation cylinders descend to spectral maps

These checks apply the generic spectral homotopy descent to the actual
right-comma BK second-coordinate cylinders. They retain the literal zero and
composition endpoints needed to construct the translation representation.
-/

open CategoryTheory Limits ZeroObject HomologicalComplex₂
open CategoryTheory.SInverseS

noncomputable section

variable {C : Type} [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{0})

example {A A' : C} (e : A ≅ A') :
    horizontalCompleteFiltrationSpectralObjectMap (secondTranslationBKBicomplexMap R A) =
      horizontalCompleteFiltrationSpectralObjectMap (secondTranslationBKBicomplexMap R A') :=
  horizontalCompleteFiltrationSpectralObjectMap_eq_of_homotopy
    ((secondTranslationDiagramScalarHomotopy e).bicomplexHomotopy AddCommGrpCat R)

example :
    horizontalCompleteFiltrationSpectralObjectMap
        (secondTranslationBKBicomplexMap R (0 : C)) =
      𝟙 (horizontalCompleteFiltrationSpectralObject
        (SSet.bkAlternatingBicomplex AddCommGrpCat R
          (SSet.rightCommaNerveDiagram (translationProjection (C := C))))) := by
  have h := horizontalCompleteFiltrationSpectralObjectMap_eq_of_homotopy
      ((secondTranslationDiagramZeroHomotopy (C := C)).bicomplexHomotopy AddCommGrpCat R)
  rw [CategoryTheory.Functor.map_id] at h
  exact h.trans ((horizontalCompleteFiltrationSpectralObjectFunctor
    (C := AddCommGrpCat.{0})).map_id _)

example (A A' : C) :
    horizontalCompleteFiltrationSpectralObjectMap
        (secondTranslationBKBicomplexMap R (A ⊞ A')) =
      horizontalCompleteFiltrationSpectralObjectMap (secondTranslationBKBicomplexMap R A') ≫
        horizontalCompleteFiltrationSpectralObjectMap (secondTranslationBKBicomplexMap R A) := by
  have h := horizontalCompleteFiltrationSpectralObjectMap_eq_of_homotopy
      ((secondTranslationDiagramBiprodHomotopy A A').bicomplexHomotopy AddCommGrpCat R)
  rw [CategoryTheory.Functor.map_comp] at h
  exact h.trans ((horizontalCompleteFiltrationSpectralObjectFunctor
    (C := AddCommGrpCat.{0})).map_comp _ _)
