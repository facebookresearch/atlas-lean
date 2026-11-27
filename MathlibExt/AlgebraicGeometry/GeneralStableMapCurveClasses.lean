/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
public import MathlibExt.AlgebraicGeometry.RelativeCurveClasses

/-!
# Curve classes of general stable-map families

For a target `X` over a field `k`, `HasCurveClass X T F β` asks that on every geometric fibre
the push-forward of the fundamental class of the source curve equals the flat pull-back of a
fixed Chow curve class `β` of `X`, tested on every cycle representing `β`. `StableFamily`
bundles a geometrically stable family with its curve class. These are split from
`GeneralStableMapFamilies` so that the core family API does not import Chow groups.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

section CurveClasses

variable {k : Type} [Field k]
    (X T : MathlibExt.AlgebraicGeometry.RelativeCurveClasses.SchemeOver k)
    {n g : ℕ} (F : Family X.hom n g T.left T.hom)

/-- The actual map of a geometric source fibre into the scalar-extended target. -/
def geometricMap (Ω : Type) [Field Ω] [Algebra k Ω]
    (p : Spec (.of Ω) ⟶ T.left)
    (hp : p ≫ T.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    (fiberCurve F.curve.π p).left ⟶
      (MathlibExt.AlgebraicGeometry.RelativeCurveClasses.fieldBaseChange X Ω).left :=
  pullback.lift (pullback.fst F.curve.π p ≫ F.map) (pullback.snd F.curve.π p) (by
    rw [Category.assoc, F.over, ← Category.assoc, pullback.condition]
    simp only [Category.assoc, hp])

/-- A fixed actual Chow curve class on every geometric fibre. The right side
is the computed native flat cycle sum, tested on every representative of β;
no arbitrary class base-change function occurs in the contract. -/
def HasCurveClass [LocallyOfFiniteType X.hom] [IsNoetherian X.left]
    (β : MathlibExt.AlgebraicGeometry.RelativeCurveClasses.CurveClass X) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (p : Spec (.of Ω) ⟶ T.left)
    (hp : p ≫ T.hom = Spec.map (CommRingCat.ofHom (algebraMap k Ω))),
    ∃ hC : IsNoetherian (fiberCurve F.curve.π p).left,
    ∃ hX : IsNoetherian
      (MathlibExt.AlgebraicGeometry.RelativeCurveClasses.fieldBaseChange X Ω).left,
    ∃ hf : IsProper (geometricMap X T F Ω p hp),
    letI := hC
    letI := hX
    letI := hf
    ∀ c : MathlibExt.AlgebraicGeometry.GeometricChow.CycleGroup X.left 1,
      (MathlibExt.AlgebraicGeometry.RelativeCurveClasses.relations X 1).mkQ c = β →
      MathlibExt.AlgebraicGeometry.RelativeCurveClasses.pushedCurveClass
        (fiberCurve F.curve.π p).left (geometricMap X T F Ω p hp) =
      (MathlibExt.AlgebraicGeometry.RelativeCurveClasses.relations
        (MathlibExt.AlgebraicGeometry.RelativeCurveClasses.fieldBaseChange X Ω) 1).mkQ
        (MathlibExt.AlgebraicGeometry.GeometricChowOperators.flatCyclePullback
          (MathlibExt.AlgebraicGeometry.RelativeCurveClasses.fieldProjection X Ω) 1 0 c)

/-- A stable map of class `β` parametrized by `T`, for schemes `X` and `T` over a field `k` with
`X` noetherian and locally of finite type over `k`: a family over `T` of `n`-marked nodal curves
of genus `g` with a map to `X` over `k` (`toFamily`), such that on every geometric fibre the
automorphisms of the marked curve commuting with the map form a finite set (`stable`), and the map
from the curve to the base change of `X` is proper and pushes the fundamental class of the curve
forward to the pullback of `β` (`curveClass`). -/
structure StableFamily [LocallyOfFiniteType X.hom] [IsNoetherian X.left]
    (β : MathlibExt.AlgebraicGeometry.RelativeCurveClasses.CurveClass X) where
  toFamily : Family X.hom n g T.left T.hom
  stable : IsGeometricallyStable toFamily
  curveClass : HasCurveClass X T toFamily β

end CurveClasses

end MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
