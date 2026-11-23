/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.NumericalCompactifiedJacobians

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.NumericalCompactifiedJacobians

universe u

variable {k : Type u} [Field k]

-- A subcurve of a proper curve is a proper curve, so Euler characteristics of
-- sheaves on it are defined.
example (C : Over (Spec (.of k))) [IsProperCurve C.hom] (Y : Subcurve C.left) :
    IsProperCurve (Y.i ≫ C.hom) := inferInstance

-- On a proper curve with `H⁰(C, 𝒪_C) = k`, the Euler characteristic of the structure
-- sheaf is `1 - g`.
example (C : Over (Spec (.of k))) [IsProperCurve C.hom] [HasConstantGlobalSections C.hom] :
    euler C.hom (structureModule C.left) = 1 - genus C.hom := by
  simp [euler, genus, finrank_cohomology_zero_structureModule]

-- Weights of a polarization: the total weight is the sum of the component weights,
-- and the weight of a subcurve only counts the components it contains.
example {C : Scheme.{u}} (c : Component C) (a : ℚ) :
    totalWeight (Finsupp.single c a : Polarization C) = a := by
  simp [totalWeight]

example {C : Scheme.{u}} (Y : Subcurve C) (c : Component C) (a : ℚ)
    (hc : ¬ c.val ⊆ Set.range Y.i) :
    subcurveWeight (Finsupp.single c a : Polarization C) Y = 0 := by
  classical
  simp [subcurveWeight, hc]

-- A stable family is tested on a parameter scheme locally of finite type over the
-- algebraically closed base field, at each of its closed (`k`-rational) points.
example [IsAlgClosed k] (C T : Over (Spec (.of k))) [IsProperCurve C.hom]
    [TorsionFreeRestrictions C.left] (q : Polarization C.left)
    (F : (prod C T).left.Modules) (hF : IsStableFamily C T q F) :
    LocallyOfFiniteType T.hom := hF.1
