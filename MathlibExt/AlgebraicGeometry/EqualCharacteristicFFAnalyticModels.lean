/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EqualCharacteristicFFSheafModels
public import MathlibExt.AlgebraicGeometry.AnalyticGroupTorsorSites

/-!
# Native analytic realizations of the equal-characteristic FF quotient

The annulus has exactly the original all-rank R+[[t]] point space and
actual rational section rings. Its stalk valuations are fixed on those
original coefficients. The curve has exactly the native Frobenius-orbit
point space and invariant structure sheaf. Its quotient retains both
the point square and the full source presheaf map.

The E=k((t)) coefficient frame fixes every original integral and Laurent
coefficient on all actual rational charts and on the native quotient map.
These are construction outputs, with no unrelated analytic curve chosen.

Source: Fargues--Scholze, arXiv:2102.13459v4, Definition I.2.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EqualCharacteristicFFAnalyticModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.TopologicalSpace _root_.AlgebraicGeometry
open EqualCharacteristicCoefficientModels EqualCharacteristicFFRingModels
open EqualCharacteristicFFSheafModels AnalyticTateAdicModels AnalyticGroupTorsorSites

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k]
  (C : ResidueData p k) (S : Base p k C) [D : RationalRestrictions p k C S]
  (F : FrobeniusPoints p k C S) (O : PeriodSheaf p k C S)
  (A : FrobeniusCharts p k C S F) (G : SheafFrobenius p k C S F O A)

/-- The source annular analytic space has the exact original point/sheaf model. -/
structure AnnularSheafModel where
  space : AnalyticAdicSpace p
  points : space.obj.space ≃ₜ ySpace p k C S
  comparison : (TopCat.Sheaf.pushforward CommRingCat
    (TopCat.ofHom ⟨points, points.continuous_toFun⟩)).obj (LocallyRingedSpace.𝒪 space.obj.space) ≅
      O.sheaf

def annularPointMap (Y : AnnularSheafModel p k C S O) :
    Y.space.obj.space.toTopCat ⟶ ySpace p k C S :=
  TopCat.ofHom ⟨Y.points, Y.points.continuous_toFun⟩

def annularOpen (Y : AnnularSheafModel p k C S O)
    (P : RationalPresentation p k C S) : Opens Y.space.obj.space :=
  (Opens.map (annularPointMap p k C S O Y)).obj P.openSet

/-- The actual original rational-ring section dictionary. -/
def annularSections (Y : AnnularSheafModel p k C S O) (P : RationalPresentation p k C S) :
    ChartRing p k C S P →+*
      Y.space.obj.space.presheaf.obj (op (annularOpen p k C S O Y P)) :=
  (Y.comparison.inv.hom.app (op P.openSet)).hom.comp
    (O.rationalComparison.inv.app (op P)).hom

/-- Every actual analytic valuation is fixed on all original period coefficients. -/
structure AnnularModel extends AnnularSheafModel p k C S O where
  valuation : ∀ (P : RationalPresentation p k C S) (x : space.obj.space)
    (hx : x ∈ annularOpen p k C S O toAnnularSheafModel P) (a b : Ring p k C S),
    (space.obj.valuation x).vle
      (space.obj.space.presheaf.germ (annularOpen p k C S O toAnnularSheafModel P) x hx
        (annularSections p k C S O toAnnularSheafModel P (chartCoefficient p k C S P a)))
      (space.obj.space.presheaf.germ (annularOpen p k C S O toAnnularSheafModel P) x hx
        (annularSections p k C S O toAnnularSheafModel P (chartCoefficient p k C S P b))) ↔
      (points x).val.val.relation.vle a b

variable (Y : AnnularModel p k C S O)

/-- The original analytic Frobenius quotient is fixed on points and its real sheaf. -/
structure QuotientModel where
  curve : AnalyticAdicSpace p
  points : curve.obj.space ≃ₜ xSpace p k C S F
  quotient : Y.space ⟶ curve
  quotient_points : ∀ x, points (quotient.hom.val.base x) =
    EqualCharacteristicFFRingModels.quotient p k C S F (Y.points x)
  comparison : (TopCat.Sheaf.pushforward CommRingCat
    (TopCat.ofHom ⟨points, points.continuous_toFun⟩)).obj (LocallyRingedSpace.𝒪 curve.obj.space) ≅
      structureSheaf p k C S F O A G
  etale : AnalyticDiamondEtaleSites.IsAnalyticEtale p quotient

variable (X : QuotientModel p k C S F O A G Y)

def curvePointMap : X.curve.obj.space.toTopCat ⟶ xSpace p k C S F :=
  TopCat.ofHom ⟨X.points, X.points.continuous_toFun⟩

def quotientPointMap : Y.space.obj.space.toTopCat ⟶ X.curve.obj.space.toTopCat :=
  X.quotient.hom.val.base

/-- The actual source quotient commutes on every native point. -/
theorem quotient_point_square :
    quotientPointMap p k C S F O A G Y X ≫ curvePointMap p k C S F O A G Y X =
      annularPointMap p k C S O Y.toAnnularSheafModel ≫
        EqualCharacteristicFFRingModels.quotient p k C S F := by
  apply TopCat.ext
  intro x
  exact X.quotient_points x

/-- Full presheaf transport uses that same actual source point square. -/
theorem quotientPresheafTransport :
    (TopCat.Presheaf.pushforward CommRingCat (curvePointMap p k C S F O A G Y X)).obj
      ((TopCat.Presheaf.pushforward CommRingCat (quotientPointMap p k C S F O A G Y X)).obj
        Y.space.obj.space.presheaf) =
    (TopCat.Presheaf.pushforward CommRingCat
      (EqualCharacteristicFFRingModels.quotient p k C S F)).obj
        ((TopCat.Presheaf.pushforward CommRingCat
          (annularPointMap p k C S O Y.toAnnularSheafModel)).obj Y.space.obj.space.presheaf) :=
  (TopCat.Presheaf.Pushforward.comp_eq _ _ _).symm.trans
    ((TopCat.Presheaf.pushforward_eq' (quotient_point_square p k C S F O A G Y X)
      Y.space.obj.space.presheaf).trans (TopCat.Presheaf.Pushforward.comp_eq _ _ _))

/-- The actual native quotient structure map retains every source open and section. -/
def quotientStructureMap :
    (TopCat.Presheaf.pushforward CommRingCat (curvePointMap p k C S F O A G Y X)).obj
      X.curve.obj.space.presheaf ⟶
    (TopCat.Presheaf.pushforward CommRingCat
      (EqualCharacteristicFFRingModels.quotient p k C S F)).obj O.sheaf.obj :=
  (TopCat.Presheaf.pushforward CommRingCat (curvePointMap p k C S F O A G Y X)).map
      X.quotient.hom.val.c ≫ eqToHom (quotientPresheafTransport p k C S F O A G Y X) ≫
    (TopCat.Presheaf.pushforward CommRingCat
      (EqualCharacteristicFFRingModels.quotient p k C S F)).map Y.comparison.hom.hom

def IsQuotientStructure : Prop :=
  quotientStructureMap p k C S F O A G Y X = X.comparison.hom.hom ≫
    (invariantInclusion p k C S F O A G).hom

/-- The actual E=k((t)) scalar frame is fixed on every original rational coefficient. -/
structure FieldFrame where
  annular : ESpace p (CoefficientField k)
  annular_normalized : annular.left = Y.space
  coefficients : ∀ (P : RationalPresentation p k C S) (e : CoefficientField k),
    (Y.space.obj.space.presheaf.map
      (homOfLE (show annularOpen p k C S O Y.toAnnularSheafModel P ≤ ⊤ from le_top)).op).hom
      (((globalRings p).map (eqToHom (congrArg op annular_normalized))).hom
        (AnalyticGroupTorsorSites.coefficients p (CoefficientField k) annular e)) =
      annularSections p k C S O Y.toAnnularSheafModel P
        (fieldCoefficients p k C S P e)
  curve : ESpace p (CoefficientField k)
  curve_normalized : curve.left = X.curve
  quotient : annular ⟶ curve
  quotient_normalized : HEq quotient.left X.quotient

variable {Y X}

/-- Native analytic outputs retain the full original quotient and E scalar frame. -/
structure AnalyticConstruction where
  annular : AnnularModel p k C S O
  quotient : QuotientModel p k C S F O A G annular
  structure_normalized : IsQuotientStructure p k C S F O A G annular quotient
  fieldFrame : FieldFrame p k C S F O A G annular quotient

end MathlibExt.AlgebraicGeometry.EqualCharacteristicFFAnalyticModels
