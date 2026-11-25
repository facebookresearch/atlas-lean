/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeFFFieldCoefficients
public import MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineMaps
public import MathlibExt.AlgebraicGeometry.AnalyticTorsorPullbacks

/-!
# The normalized affine Perf family of relative FF curves

Every object retains its actual ramified annular rings, coefficient
field, Frobenius orbit, invariant structure sheaf and analytic quotient.
Base change fixes every original coefficient on every rational chart
and the entire quotient square. The family functor is computed from
these displayed object/morphism data and their identity/composition
laws. It is not base change of one absolute curve.

The geometric family constructor and torsor v-descent remain separate
requests. This file does not assume that Bun_G is a v-stack.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections I.2 and III.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeFFCurveFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open LocalWittCoefficientFields LocalCoefficientScalarFrames RelativeFarguesFontaineRings
open RelativeFarguesFontaineMaps RelativeFFAnalyticModels RelativeFFFieldCoefficients
open AnalyticGroupTorsorSites

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)
  (F : IntegerPresentation p C)

/-- One exact relative curve realization with its original scalar map. -/
structure Frame (S : Base p C) where
  source : Source p C S
  annular : AnnularModel (D := source.restrictions) p C S source.period
  quotient : QuotientModel (D := source.restrictions) p C S source.phi source.period
    source.sheafMap annular
  normalized : IsQuotientStructure (D := source.restrictions) p C S source.phi source.period
    source.sheafMap annular quotient
  scalars : FieldMap (D := source.restrictions) p C F S source.phi source.period source.sheafMap
    annular quotient

variable {S : Base p C}

def Frame.object (A : Frame p C F S) : ESpace p E.field := by
  letI := A.source.restrictions
  exact curveObject p C F S A.source.phi A.source.period A.source.sheafMap
    A.annular A.quotient A.scalars

def Frame.annularSpace (A : Frame p C F S) : AnalyticTateAdicModels.AnalyticAdicSpace p := by
  letI := A.source.restrictions
  exact A.annular.space

def Frame.curveSpace (A : Frame p C F S) : AnalyticTateAdicModels.AnalyticAdicSpace p := by
  letI := A.source.restrictions
  exact A.quotient.curve

def Frame.annularPoints (A : Frame p C F S) :
    (A.annularSpace p C F).obj.space ≃ₜ ySpace p C S := by
  letI := A.source.restrictions
  exact A.annular.points

def Frame.quotientMap (A : Frame p C F S) : A.annularSpace p C F ⟶ A.curveSpace p C F := by
  letI := A.source.restrictions
  exact A.quotient.quotient

def Frame.annularOpen (A : Frame p C F S) (P : RationalPresentation p C S) :
    Opens (A.annularSpace p C F).obj.space := by
  letI := A.source.restrictions
  exact RelativeFFAnalyticModels.annularOpen p C S A.source.period A.annular.toAnnularSheafModel P

def Frame.annularCoefficient (A : Frame p C F S) (P : RationalPresentation p C S) :
    Ring p C S →+* (A.annularSpace p C F).obj.space.presheaf.obj
      (op (A.annularOpen p C F P)) := by
  letI := A.source.restrictions
  exact (RelativeFFAnalyticModels.annularSections p C S A.source.period
    A.annular.toAnnularSheafModel P).comp (chartCoefficient p C S P)

def Frame.pointMap (A : Frame p C F S) : (A.curveSpace p C F).obj.space.toTopCat ⟶
    xSpace p C S A.source.phi := by
  letI := A.source.restrictions
  exact curvePointMap p C S A.source.phi A.source.period A.source.sheafMap
    A.annular A.quotient

variable {T : Base p C} (A : Frame p C F S) (B : Frame p C F T) (f : S ⟶ T)

/-- Every base-change component is fixed on source annular points, sections and quotient maps. -/
structure BaseChange where
  points : PointMap p C A.source B.source f
  annular : A.annularSpace p C F ⟶ B.annularSpace p C F
  annular_points : ∀ x : (A.annularSpace p C F).obj.space,
    B.annularPoints p C F (annular.hom.val.base x) = points.map (A.annularPoints p C F x)
  map : A.object p C F ⟶ B.object p C F
  quotient_square : annular ≫ B.quotientMap p C F = A.quotientMap p C F ≫ map.left
  curve_points : A.pointMap p C F ≫ orbitMap p C A.source B.source f points =
    map.left.hom.val.base ≫ B.pointMap p C F
  coefficients : ∀ (P : RationalPresentation p C S) (Q : RationalPresentation p C T)
    (h : A.annularOpen p C F P ≤
      (Opens.map annular.hom.val.base).obj (B.annularOpen p C F Q)) (a : Ring p C T),
    (A.annularSpace p C F).obj.space.presheaf.map (homOfLE h).op
      (annular.hom.val.c.app (op (B.annularOpen p C F Q)) (B.annularCoefficient p C F Q a)) =
        A.annularCoefficient p C F P (periodMap p C f a)

/-- The family retains these exact native components before bundling their functor. -/
structure Family where
  frame : ∀ S : Base p C, Frame p C F S
  change : ∀ {S T : Base p C} (f : S ⟶ T), BaseChange p C F (frame S) (frame T) f
  identity : ∀ S, (change (𝟙 S)).map = 𝟙 ((frame S).object p C F)
  composition : ∀ {S T U : Base p C} (f : S ⟶ T) (g : T ⟶ U),
    (change (f ≫ g)).map = (change f).map ≫ (change g).map

/-- The actual source curve functor has its specified relative rings at each base. -/
def Family.toFunctor (A : Family p C F) : Base p C ⥤ ESpace p E.field where
  obj S := (A.frame S).object p C F
  map f := (A.change f).map
  map_id S := A.identity S
  map_comp f g := A.composition f g

end MathlibExt.AlgebraicGeometry.RelativeFFCurveFamilies
