/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier.lean`,
`Theorems/Thm_AlgebraicGeometry_SchemeHomOver_eq_of_isSeparated_of_valuationRing_of_fst_eq.lean`
and
`P2M/Sol/S_AlgebraicGeometry_SchemeHomOver_eq_of_isSeparated_of_valuationRing_of_fst_eq.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Morphisms of schemes over a common base

A morphism over a common base is a morphism whose composite with the
structure morphism of the target is the structure morphism of the source.
Two such morphisms into a separated scheme over a valuation ring are
equal if they agree after restriction to the fraction field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes over a common base: a morphism `φ : Y ⟶ X` with
`φ ≫ f = g`. -/
abbrev SchemeHomOver {B Y X : Scheme.{u}} (g : Y ⟶ B) (f : X ⟶ B) :=
  { φ : Y ⟶ X // φ ≫ f = g }

/-- Two points of a separated scheme over a valuation ring agree if their
generic fibres agree. -/
theorem SchemeHomOver.eq_of_isSeparated_of_valuationRing_of_fst_eq
    {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}
    [IsSeparated f]
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] [Algebra R A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K]
    (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f)
    (h : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x.1 =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ y.1) :
    x = y := by
  have hw : (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x.1) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [Category.assoc, x.2]
  let sq : ValuativeCommSq f :=
    { R := A, K := K,
      i₁ := Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x.1,
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap R A)),
      commSq := ⟨hw⟩ }
  have hsub : Subsingleton sq.commSq.LiftStruct := IsSeparated.valuativeCriterion f sq
  let lx : sq.commSq.LiftStruct := ⟨x.1, rfl, x.2⟩
  let ly : sq.commSq.LiftStruct := ⟨y.1, h.symm, y.2⟩
  have hlxy : lx = ly := hsub.elim lx ly
  have hxy1 : x.1 = y.1 := congrArg CommSq.LiftStruct.l hlxy
  exact Subtype.ext hxy1

end AlgebraicGeometry
