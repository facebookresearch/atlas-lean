/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoend
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.ZMod.Defs

/-! The coend of a representable weight against the two-element group's action on `Bool`. -/

open CategoryTheory MonoidalCategory Opposite Limits
open scoped MonoidalClosed

noncomputable section

namespace MathlibExtTest.WeightedCoendBoolAction

private abbrev FlipGroup := Multiplicative (ZMod 2)
private abbrev Index := SingleObj FlipGroup

local instance : EnrichedCategory (Type) Index := enrichedCategoryTypeOfCategory Index

private def act (g : FlipGroup) (value : Bool) : Bool :=
  if Multiplicative.toAdd g = 0 then value else !value

private theorem act_mul (g h : FlipGroup) (value : Bool) :
    act (g * h) value = act g (act h value) := by
  have two : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases two (Multiplicative.toAdd g) with hg | hg <;>
    rcases two (Multiplicative.toAdd h) with hh | hh <;>
    cases value <;> simp [act, toAdd_mul, hg, hh] <;> decide

private def diagram : EnrichedFunctor (Type) Index (Type) where
  obj _ := Bool
  map _ _ := ↾fun g => (↾fun value => act g value : Bool ⟶ Bool)
  map_id _ := by
    ext ⟨⟩
    change (_ : Bool ⟶ Bool) = _
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    rfl
  map_comp _ _ _ := by
    ext ⟨f, g⟩
    change (_ : Bool ⟶ Bool) = _
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact act_mul g f value

private abbrev star : Index := SingleObj.star FlipGroup
private abbrev weight : EnrichedFunctor (Type) Indexᵒᵖ (Type) :=
  EnrichedFunctor.contravariantRepresentable (Type) Index star
private abbrev generator := Enriched.weightedCoend.ι weight diagram star
private abbrev comparison := Enriched.weightedCoend.coyonedaIso diagram star
private abbrev flip : FlipGroup := Multiplicative.ofAdd (1 : ZMod 2)

private theorem generator_value (g : FlipGroup) (value : Bool) :
    (generator ≫ comparison.hom) (g, value) = act g value := by
  change (Enriched.weightedCoend.ι weight diagram star ≫
    (Enriched.weightedCoend.coyonedaIso diagram star).hom) (g, value) = _
  rw [Enriched.weightedCoend.coyonedaIso_ι_hom]
  rfl

private theorem generator_flip : (generator ≫ comparison.hom) (flip, true) = false :=
  (generator_value _ _).trans rfl

private theorem generator_unit : (generator ≫ comparison.hom) ((1 : FlipGroup), true) = true :=
  (generator_value _ _).trans rfl

private theorem comparison_inv_value (value : Bool) :
    comparison.inv value = generator ((1 : FlipGroup), value) := by
  rw [Enriched.weightedCoend.coyonedaIso_inv]
  rfl

-- Test the balancing relation in the coend itself, before applying the comparison.
private theorem generator_balance (g h : FlipGroup) (value : Bool) :
    generator (g * h, value) = generator (g, act h value) :=
  congrArg (fun f => f (g, (h, value)))
    (Enriched.weightedCoend.condition weight diagram star star)

private theorem generator_flip_balances : generator (flip, true) =
    generator ((1 : FlipGroup), false) := by
  have flipTrue : act flip true = false := rfl
  simpa only [one_mul, flipTrue] using generator_balance 1 flip true

end MathlibExtTest.WeightedCoendBoolAction
