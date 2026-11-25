/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Adjunction.RelativeLifting
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Extension into coextended modules

The restriction–coextension adjunction extends maps into coextended modules across scalar-split
monomorphisms. The extension factors through the given map and has a scalar, retraction, and
evaluation formula. The scalar rings are associative and the module categories use the stated
common universe.
-/

@[expose] public section

noncomputable section
open CategoryTheory
universe u v w

namespace ModuleCat.CoextendScalars

variable {k : Type u} {R : Type v} [Ring k] [Ring R] (φ : k →+* R)

/-- Extend an map into a coextended object through a scalar retraction. -/
def extendOfRestrictedSplitMono (N : ModuleCat.{max v w} k)
    {X X' : ModuleCat.{max v w} R} (g : X ⟶ X')
    (s : SplitMono ((ModuleCat.restrictScalars.{max v w} φ).map g))
    (f : X ⟶ (ModuleCat.coextendScalars φ).obj N) :
    X' ⟶ (ModuleCat.coextendScalars φ).obj N :=
  (ModuleCat.restrictCoextendScalarsAdj φ).extendOfSplitMono g s f

/-- Restricting the extension along the mono recovers the map. -/
@[reassoc]
theorem comp_extendOfRestrictedSplitMono (N : ModuleCat.{max v w} k)
    {X X' : ModuleCat.{max v w} R} (g : X ⟶ X')
    (s : SplitMono ((ModuleCat.restrictScalars.{max v w} φ).map g))
    (f : X ⟶ (ModuleCat.coextendScalars φ).obj N) :
    g ≫ extendOfRestrictedSplitMono φ N g s f = f :=
  (ModuleCat.restrictCoextendScalarsAdj φ).comp_extendOfSplitMono g s f

/-- The extension has the scalar/retraction/evaluation value on every element. -/
theorem extendOfRestrictedSplitMono_apply (N : ModuleCat.{max v w} k)
    {X X' : ModuleCat.{max v w} R} (g : X ⟶ X')
    (s : SplitMono ((ModuleCat.restrictScalars.{max v w} φ).map g))
    (f : X ⟶ (ModuleCat.coextendScalars φ).obj N) (x : X') (r : R) :
    extendOfRestrictedSplitMono φ N g s f x r =
      f (show X from s.retraction (r • x)) (1 : R) := by
  dsimp only [extendOfRestrictedSplitMono, Adjunction.extendOfSplitMono]
  rw [Adjunction.homEquiv_unit]
  change ((ModuleCat.restrictCoextendScalarsAdj φ).homEquiv X N).symm f
    (s.retraction (r • x)) = _
  rw [Adjunction.homEquiv_counit]
  rfl

end ModuleCat.CoextendScalars
end
