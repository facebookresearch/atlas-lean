/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
public import MathlibExt.AlgebraicGeometry.BirationalResolution
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual dominating two-point rational-curve families

A family is an actual morphism C × S → X, where C is a smooth proper
geometrically irreducible genus-zero curve with two distinct field points.
The parameter scheme S is integral and of finite type. Evaluation at those
two fixed points is an actual dominant map S → X × X.

This definition supplies neither a free rational-connectedness predicate
nor an assumed tangent/cohomology operator. On smooth projective varieties
in characteristic zero it is the usual rational-connectedness condition.

References: Kollár, *Rational Curves on Algebraic Varieties*, Chapter IV;
Campana and Kollár–Miyaoka–Mori, rational connectedness of Fano varieties.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RationalCurveFamilies

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

universe u

abbrev productOver {k : Type u} [Field k]
    (X Y : Over (Spec (.of k))) : Over (Spec (.of k)) :=
  Over.mk (pullback.fst X.hom Y.hom ≫ X.hom)

def endpoint {k : Type u} [Field k]
    {C S : Over (Spec (.of k))} (p : Over.mk (𝟙 (Spec (.of k))) ⟶ C) :
    S ⟶ productOver C S :=
  Over.homMk (pullback.lift (S.hom ≫ p.left) (𝟙 S.left) (by
    simp [Category.assoc, p.w])) (by
      simp [productOver, Category.assoc, p.w])

def pairEvaluation {k : Type u} [Field k]
    {C S X : Over (Spec (.of k))}
    (p q : Over.mk (𝟙 (Spec (.of k))) ⟶ C) (f : productOver C S ⟶ X) :
    S ⟶ productOver X X :=
  Over.homMk (pullback.lift ((endpoint p ≫ f).left) ((endpoint q ≫ f).left)
    (by rw [(endpoint p ≫ f).w, (endpoint q ≫ f).w])) (by
      change pullback.lift _ _ _ ≫
        (pullback.fst X.hom X.hom ≫ X.hom) = S.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact (endpoint p ≫ f).w)

structure RationalCurveFamily {k : Type u} [Field k]
    (X : Over (Spec (.of k))) where
  curve : Over (Spec (.of k))
  [properCurve : IsProper curve.hom]
  [smoothCurve : SmoothOfRelativeDimension 1 curve.hom]
  [irreducibleCurve : GeometricallyIrreducible curve.hom]
  /-- Genus zero: `h¹(C, 𝒪_C) = 0`, the genus of this smooth proper geometrically irreducible
  curve (for which `H⁰(C, 𝒪_C) = k`). -/
  genus_zero : Module.finrank k (cohomology curve.hom (structureModule curve.left) 1) = 0
  firstPoint : Over.mk (𝟙 (Spec (.of k))) ⟶ curve
  secondPoint : Over.mk (𝟙 (Spec (.of k))) ⟶ curve
  distinct : firstPoint ≠ secondPoint
  parameter : Over (Spec (.of k))
  [integralParameter : IsIntegral parameter.left]
  [finiteTypeParameter : LocallyOfFiniteType parameter.hom]
  [compactParameter : QuasiCompact parameter.hom]
  map : productOver curve parameter ⟶ X
  dominant : IsDominant (pairEvaluation firstPoint secondPoint map).left

def IsRationallyConnected {k : Type u} [Field k]
    (X : Over (Spec (.of k))) : Prop := Nonempty (RationalCurveFamily X)

end MathlibExt.AlgebraicGeometry.RationalCurveFamilies
