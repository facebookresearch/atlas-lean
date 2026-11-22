/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Original source colimits under a contravariant limit-preserving functor

The generic mapped cone, universal lifts and all projection equations are
retained from the native ordinal mapping-limit source, before any spectrum
functor is selected. Source and target categories and diagram universes remain
independent.
-/

set_option autoImplicit false
noncomputable section
universe u v w w' uC vC uV vV
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.OriginalSourceMappingLimit

variable {C : Type uC} [Category.{vC} C] {V : Type uV} [Category.{vV} V]
  {J : Type w} [Category.{w'} J] (G : Cᵒᵖ ⥤ V)

/-- Fix the entire source functor before mapping the caller's original diagram. -/
def diagram (F : J ⥤ C) : Jᵒᵖ ⥤ V := F.op ⋙ G

/-- The actual mapping cone keeps the original source cocone and all its maps. -/
def cone {F : J ⥤ C} (c : Cocone F) : Cone (diagram G F) := G.mapCone c.op

/-- Actual preservation by the fixed source functor gives the full original mapped limit. -/
def isLimit [PreservesLimitsOfSize.{w', w} G]
    {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c) : IsLimit (cone G c) :=
  isLimitOfPreserves G hc.op

/-- The original universal limit lift of any full mapped source cone. -/
def lift [PreservesLimitsOfSize.{w', w} G]
    {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c) (s : Cone (diagram G F)) :
    s.pt ⟶ (cone G c).pt := (isLimit G c hc).lift s

/-- All full original restriction maps are retained by that universal lift. -/
theorem lift_π [PreservesLimitsOfSize.{w', w} G]
    {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c)
    (s : Cone (diagram G F)) (j : Jᵒᵖ) :
    lift G c hc s ≫ (cone G c).π.app j = s.π.app j := (isLimit G c hc).fac s j

/-- All original projection maps detect equality in the actual mapped source limit. -/
theorem hom_ext [PreservesLimitsOfSize.{w', w} G]
    {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c) {T : V}
    {a b : T ⟶ (cone G c).pt}
    (h : ∀ j : Jᵒᵖ, a ≫ (cone G c).π.app j = b ≫ (cone G c).π.app j) : a = b :=
  (isLimit G c hc).hom_ext h

/-- The actual universal lift and all of its projection equations are constructed together
from one fixed limiting cone, before choosing the native source functor. -/
structure ChosenLift {F : J ⥤ V} (c s : Cone F) where
  /-- The complete original universal map. -/
  hom : s.pt ⟶ c.pt
  /-- Every actual original projection equation. -/
  fac (j : J) : hom ≫ c.π.app j = s.π.app j

/-- Construct the lift data using the same original limiting witness. -/
def chosenLift {F : J ⥤ V} (c : Cone F) (hc : IsLimit c) (s : Cone F) : ChosenLift c s where
  hom := hc.lift s
  fac := hc.fac s

/-- The constructed map is precisely the original limiting witness's lift. -/
theorem chosenLift_hom {F : J ⥤ V} (c : Cone F) (hc : IsLimit c) (s : Cone F) :
    (chosenLift c hc s).hom = hc.lift s := rfl

end CategoryTheory.OriginalSourceMappingLimit
