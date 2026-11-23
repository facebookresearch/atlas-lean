/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomologyBicomplex
public import MathlibExt.Algebra.Homology.Functor
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationCommaDiagram
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# BK maps induced by additive S⁻¹S translation

The natural transformation of translated right-comma nerve diagrams maps
functorially through the existing Bousfield--Kan alternating bicomplex and
total-complex functors.  The resulting total chain map is the totalization of
the bicomplex map, and hence induces a named map on total homology.

This file does not identify the precomposed target diagram with the original
diagram, compute the vertical-homology action, compare with the homology map
of `translateFirstFunctor`, localize, realize, or use CGWH.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

/-- Canonical universe-u additive colimits for translated BK maps. -/
noncomputable local instance translationBKMapAdditiveColimits :
    HasColimitsOfSize.{u, u} AddCommGrpCat.{u} :=
  { has_colimits_of_shape := fun (J : Type u) (hJ : Category.{u} J) => by
      letI : Category.{u} J := hJ
      letI : Small.{u} J := small_self J
      exact AddCommGrpCat.hasColimitsOfShape.{u, u, u} (J := J) }

/-- Canonical universe-u additive coproducts for translated BK maps. -/
noncomputable local instance translationBKMapAdditiveCoproducts :
    HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun (J : Type u) => by
    let _ : HasColimitsOfSize.{u, u} AddCommGrpCat.{u} := translationBKMapAdditiveColimits
    exact HasColimitsOfSize.has_colimits_of_shape (C := AddCommGrpCat.{u}) (J := Discrete J)

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

local notation "c" => ComplexShape.down ℕ

/-- The translated target of the right-comma nerve diagram. -/
noncomputable abbrev translatedRightCommaNerveDiagram (A : C) :
    Translation C ⥤ SSet.{u} :=
  Translation.translateFunctor A ⋙
    SSet.rightCommaNerveDiagram (translationProjection (C := C))

/-- Bousfield--Kan bicomplex map induced by first-coordinate translation. -/
noncomputable def translationBKBicomplexMap
    (R : AddCommGrpCat.{u}) (A : C) :
    SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R
        (SSet.rightCommaNerveDiagram (translationProjection (C := C))) ⟶
      SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R
        (translatedRightCommaNerveDiagram C A) :=
  (SSet.bkAlternatingBicomplexFunctor AddCommGrpCat.{u} R).map
    (translationRightCommaNerveDiagramNatTrans A)

/-- Total chain map induced by first-coordinate translation of the
right-comma diagram. -/
noncomputable def translationBKTotalComplexMap
    (R : AddCommGrpCat.{u}) (A : C) :
    SSet.bkAlternatingTotalComplex AddCommGrpCat.{u} R
        (SSet.rightCommaNerveDiagram (translationProjection (C := C))) ⟶
      SSet.bkAlternatingTotalComplex AddCommGrpCat.{u} R
        (translatedRightCommaNerveDiagram C A) :=
  (SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{u} R).map
    (translationRightCommaNerveDiagramNatTrans A)

/-- The direct BK total map is the totalization of the translated BK
bicomplex map. -/
theorem translationBKTotalComplexMap_eq_totalFunctor_map
    (R : AddCommGrpCat.{u}) (A : C) :
    translationBKTotalComplexMap C R A =
      (HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} c c c).map
        (translationBKBicomplexMap C R A) :=
  rfl

/-- Map on BK total homology induced by first-coordinate translation. -/
noncomputable def translationBKTotalHomologyMap
    (R : AddCommGrpCat.{u}) (A : C) (n : ℕ) :
    (SSet.bkAlternatingTotalComplex AddCommGrpCat.{u} R
        (SSet.rightCommaNerveDiagram
          (translationProjection (C := C)))).homology n ⟶
      (SSet.bkAlternatingTotalComplex AddCommGrpCat.{u} R
        (translatedRightCommaNerveDiagram C A)).homology n :=
  HomologicalComplex.homologyMap
    (translationBKTotalComplexMap C R A) n

end SInverseS
end CategoryTheory

end
