/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomOpenBox

/-!
# Relative lifting of the coherent Hom open box

The scalar anodyne inclusion lifts against a 
Kan–Quillen fibration, retaining both the prescribed box map and
the prescribed target Hom map. No ambient source or target Kan
hypothesis and no enriched model outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.CoherentRealization.RelativeOpenBox

variable {J : Type u} [LinearOrder J] {i j : J}

/-- A coherent open-box square lifts through a scalar fibration with both
full equations. -/
theorem exists_fill (hij : i ≤ j) (k : IntervalHom.Interior i j)
    {X Y : SSet.{u}} (p : X ⟶ Y) [Fibration p]
    (f : (HomOpenBox.subcomplex hij k : SSet.{u}) ⟶ X)
    (g : nerve (SimplicialThickening.Path i j) ⟶ Y)
    (sq : CommSq f (HomOpenBox.subcomplex hij k).ι p g) :
    ∃ l : nerve (SimplicialThickening.Path i j) ⟶ X,
      (HomOpenBox.subcomplex hij k).ι ≫ l = f ∧ l ≫ p = g := by
  let _ : HasLiftingProperty (HomOpenBox.subcomplex hij k).ι p :=
    HomOpenBox.subcomplex_anodyne hij k p (by rwa [← fibration_iff])
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end CategoryTheory.CoherentRealization.RelativeOpenBox
