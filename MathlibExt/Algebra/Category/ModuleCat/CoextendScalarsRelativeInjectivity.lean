/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Adjunction.RelativeInjectivity
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Relative injectivity of coextended modules

The restriction–coextension adjunction makes coextended modules injective relative to scalar
restriction. Relative injectivity is equivalent to splitting the unit and to being a retract of a
coextended module.
-/

@[expose] public section

open CategoryTheory
universe u v w

namespace ModuleCat.CoextendScalars

variable {k : Type u} {R : Type v} [Ring k] [Ring R] (φ : k →+* R)

/-- Every coextended object has the full scalar-relative extension property. -/
theorem isRelativeInjective_obj (N : ModuleCat.{max v w} k) :
    (ModuleCat.restrictScalars.{max v w} φ).IsRelativeInjective
      ((ModuleCat.coextendScalars φ).obj N) :=
  (ModuleCat.restrictCoextendScalarsAdj φ).isRelativeInjective_obj N

/-- The restriction/coextension unit splits exactly for relatively injective modules. -/
theorem isRelativeInjective_iff_unit_isSplitMono (P : ModuleCat.{max v w} R) :
    (ModuleCat.restrictScalars.{max v w} φ).IsRelativeInjective P ↔
      IsSplitMono ((ModuleCat.restrictCoextendScalarsAdj φ).unit.app P) :=
  (ModuleCat.restrictCoextendScalarsAdj φ).isRelativeInjective_iff_unit_isSplitMono P

/-- The full extension property is equivalent to being a retract of an coextension. -/
theorem isRelativeInjective_iff_retract_coextended (P : ModuleCat.{max v w} R) :
    (ModuleCat.restrictScalars.{max v w} φ).IsRelativeInjective P ↔
      ∃ N : ModuleCat.{max v w} k, Nonempty (Retract P ((ModuleCat.coextendScalars φ).obj N)) :=
  (ModuleCat.restrictCoextendScalarsAdj φ).isRelativeInjective_iff_retract_cofree P

end ModuleCat.CoextendScalars
