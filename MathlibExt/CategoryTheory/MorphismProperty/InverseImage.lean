/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
Base-change stability passes to `P.inverseImage F` when `F` preserves
`WalkingCospan` limits. This file makes no converse, reflection, or
limit-existence claim.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.MorphismProperty

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- Base-change stability for `P.inverseImage F`.

Hypotheses: `P.IsStableUnderBaseChange` and `PreservesLimitsOfShape WalkingCospan F`.
Given a pullback square `sq` in `C` with stable leg, the mapped square `sq.map F`
in `D` is the pullback to which `P`'s stability applies. -/
theorem isStableUnderBaseChange_inverseImage {P : MorphismProperty D} (F : C ⥤ D)
    [P.IsStableUnderBaseChange] [PreservesLimitsOfShape WalkingCospan F] :
    (P.inverseImage F).IsStableUnderBaseChange where
  of_isPullback {X Y Y' S f g f' g'} sq hg := by
    have hD : IsPullback (F.map f') (F.map g') (F.map g) (F.map f) := sq.map F
    exact IsStableUnderBaseChange.of_isPullback (P := P) hD hg

/-- Typeclass wrapper for `isStableUnderBaseChange_inverseImage`. -/
instance {P : MorphismProperty D} (F : C ⥤ D) [P.IsStableUnderBaseChange]
    [PreservesLimitsOfShape WalkingCospan F] :
    (P.inverseImage F).IsStableUnderBaseChange :=
  isStableUnderBaseChange_inverseImage F

end CategoryTheory.MorphismProperty

noncomputable section
universe uC vC uD vD

namespace CategoryTheory.MorphismProperty

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- An actual natural isomorphism identifies the entire inverse-image morphism property. -/
theorem inverseImage_eq_of_natIso (P : MorphismProperty D) [P.RespectsIso]
    {F G : C ⥤ D} (e : F ≅ G) : P.inverseImage F = P.inverseImage G := by
  ext X Y f
  exact P.arrow_mk_iso_iff (((Functor.mapArrowFunctor C D).mapIso e).app (Arrow.mk f))

/-- The original counit recovers every target arrow in a full property roundtrip. -/
theorem inverseImage_equivalence_roundtrip (P : MorphismProperty D) [P.RespectsIso]
    (e : C ≌ D) :
    (P.inverseImage e.functor).inverseImage e.inverse = P := by
  rw [inverseImage_inverseImage, inverseImage_eq_of_natIso P e.counitIso, inverseImage_id]

/-- The original unit recovers every source arrow in the reverse full property roundtrip. -/
theorem inverseImage_equivalence_reverse_roundtrip (P : MorphismProperty C) [P.RespectsIso]
    (e : C ≌ D) :
    (P.inverseImage e.inverse).inverseImage e.functor = P := by
  rw [inverseImage_inverseImage, inverseImage_eq_of_natIso P e.unitIso.symm, inverseImage_id]

end CategoryTheory.MorphismProperty
