/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineSheaves
public import MathlibExt.AlgebraicGeometry.AnalyticGroupTorsorSites

/-!
# Analytic realizations of the actual relative FF quotient

The annular model has exactly the original doubly punctured valuation
space and actual rational section rings. Every stalk valuation is
normalized on the original ramified Witt coefficients. The curve has
exactly its Frobenius orbit space and invariant structure sheaf.
Its quotient map is pinned both on points and on the full native
structure-presheaf map, not only on global constants.

These are normalized geometric construction outputs. The completed
generic local realization/gluing source is reused; a general local-field
FF realization theorem is not claimed here.
Source: Fargues--Scholze, arXiv:2102.13459v4, Definition I.2.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeFFAnalyticModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open LocalWittCoefficientFields RelativeFarguesFontaineRings
open RelativeFarguesFontaineSheaves AnalyticTateAdicModels

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E) (S : Base p C)
  [D : RationalRestrictions p C S] (φ : FrobeniusPoints p C S) (O : PeriodSheaf p C S)
  (g : O.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat (frobeniusMap p C S φ)).obj O.sheaf)

structure AnnularSheafModel where
  space : AnalyticAdicSpace p
  points : space.obj.space ≃ₜ ySpace p C S
  comparison : (TopCat.Sheaf.pushforward CommRingCat
    (TopCat.ofHom ⟨points, points.continuous_toFun⟩)).obj (LocallyRingedSpace.𝒪 space.obj.space) ≅
      O.sheaf

def annularPointMap (A : AnnularSheafModel p C S O) : A.space.obj.space.toTopCat ⟶
    ySpace p C S := TopCat.ofHom ⟨A.points, A.points.continuous_toFun⟩

def annularOpen (A : AnnularSheafModel p C S O) (P : RationalPresentation p C S) :
    Opens A.space.obj.space := (Opens.map (annularPointMap p C S O A)).obj P.openSet

/-- Each section dictionary is the inverse of the actual source comparisons. -/
def annularSections (A : AnnularSheafModel p C S O) (P : RationalPresentation p C S) :
    ChartRing p C S P →+* A.space.obj.space.presheaf.obj (op (annularOpen p C S O A P)) :=
  (A.comparison.inv.hom.app (op P.openSet)).hom.comp
    (O.rationalComparison.inv.app (op P)).hom

structure AnnularModel extends AnnularSheafModel p C S O where
  valuation : ∀ (P : RationalPresentation p C S) (x : space.obj.space)
    (hx : x ∈ annularOpen p C S O toAnnularSheafModel P) (a b : Ring p C S),
    (space.obj.valuation x).vle
      (space.obj.space.presheaf.germ (annularOpen p C S O toAnnularSheafModel P) x hx
        (annularSections p C S O toAnnularSheafModel P (chartCoefficient p C S P a)))
      (space.obj.space.presheaf.germ (annularOpen p C S O toAnnularSheafModel P) x hx
        (annularSections p C S O toAnnularSheafModel P (chartCoefficient p C S P b))) ↔
      (points x).val.val.relation.vle a b

variable (A : AnnularModel p C S O)

structure QuotientModel where
  curve : AnalyticAdicSpace p
  points : curve.obj.space ≃ₜ xSpace p C S φ
  quotient : A.space ⟶ curve
  quotient_points : ∀ x : A.space.obj.space,
    points (quotient.hom.val.base x) = RelativeFarguesFontaineRings.quotient p C S φ (A.points x)
  comparison : (TopCat.Sheaf.pushforward CommRingCat
    (TopCat.ofHom ⟨points, points.continuous_toFun⟩)).obj (LocallyRingedSpace.𝒪 curve.obj.space) ≅
      structureSheaf p C S φ O g
  etale : AnalyticDiamondEtaleSites.IsAnalyticEtale p quotient

variable (Q : QuotientModel p C S φ O g A)

def curvePointMap : Q.curve.obj.space.toTopCat ⟶ xSpace p C S φ :=
  TopCat.ofHom ⟨Q.points, Q.points.continuous_toFun⟩

def quotientPointMap : A.space.obj.space.toTopCat ⟶ Q.curve.obj.space.toTopCat :=
  Q.quotient.hom.val.base

theorem quotient_point_square :
    quotientPointMap p C S φ O g A Q ≫ curvePointMap p C S φ O g A Q =
      annularPointMap p C S O A.toAnnularSheafModel ≫
        RelativeFarguesFontaineRings.quotient p C S φ := by
  apply TopCat.ext
  intro x
  exact Q.quotient_points x

/-- The full presheaf transport follows the displayed native point square. -/
theorem quotientPresheafTransport :
    (TopCat.Presheaf.pushforward CommRingCat (curvePointMap p C S φ O g A Q)).obj
      ((TopCat.Presheaf.pushforward CommRingCat (quotientPointMap p C S φ O g A Q)).obj
        A.space.obj.space.presheaf) =
    (TopCat.Presheaf.pushforward CommRingCat (RelativeFarguesFontaineRings.quotient p C S φ)).obj
      ((TopCat.Presheaf.pushforward CommRingCat
        (annularPointMap p C S O A.toAnnularSheafModel)).obj A.space.obj.space.presheaf) :=
  (TopCat.Presheaf.Pushforward.comp_eq _ _ _).symm.trans
    ((TopCat.Presheaf.pushforward_eq' (quotient_point_square p C S φ O g A Q)
      A.space.obj.space.presheaf).trans (TopCat.Presheaf.Pushforward.comp_eq _ _ _))

/-- The analytic quotient's actual native structure-presheaf map. -/
def quotientStructureMap :
    (TopCat.Presheaf.pushforward CommRingCat (curvePointMap p C S φ O g A Q)).obj
      Q.curve.obj.space.presheaf ⟶
    (TopCat.Presheaf.pushforward CommRingCat (RelativeFarguesFontaineRings.quotient p C S φ)).obj
      O.sheaf.obj :=
  (TopCat.Presheaf.pushforward CommRingCat (curvePointMap p C S φ O g A Q)).map
      Q.quotient.hom.val.c ≫ eqToHom (quotientPresheafTransport p C S φ O g A Q) ≫
    (TopCat.Presheaf.pushforward CommRingCat (RelativeFarguesFontaineRings.quotient p C S φ)).map
      A.comparison.hom.hom

/-- Equality is required on every open and every section of the actual source sheaf. -/
def IsQuotientStructure : Prop :=
  quotientStructureMap p C S φ O g A Q = Q.comparison.hom.hom ≫
    (invariantInclusion p C S φ O g).hom

end MathlibExt.AlgebraicGeometry.RelativeFFAnalyticModels
