/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# Actual scalar open-box lifting for coherent Hom cubes

For an actual subcomplex A of X, the upper open box is
A times the interval union X times its upper endpoint. Its inclusion is
an anodyne extension by the pinned scalar pushout-product theorem. Every
actual map from that box into a Kan complex has an actual extension with
the exact original restriction equation. No enriched model or lifting
outcome is supplied as an input.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OpenBox

/-- The actual upper scalar open box, retaining the whole supplied boundary subcomplex. -/
def upper {X : SSet.{u}} (A : X.Subcomplex) : (X ⊗ Δ[1]).Subcomplex :=
  A.unionProd (Λ[1, (1 : Fin 2)])

/-- This actual scalar inclusion has the left lifting property against all genuine scalar
fibrations. -/
theorem upper_anodyne {X : SSet.{u}} (A : X.Subcomplex) :
    SSet.anodyneExtensions (upper A).ι :=
  SSet.anodyneExtensions_unionProd_ι A Λ[1, (1 : Fin 2)] (SSet.anodyneExtensions.horn_ι _)

open SSet.modelCategoryQuillen in
/-- Any actual upper open-box map into a Kan complex extends on the actual whole scalar product. -/
theorem exists_fill {X Y : SSet.{u}} (A : X.Subcomplex) [SSet.KanComplex Y]
    (f : (upper A : SSet) ⟶ Y) : ∃ g : X ⊗ Δ[1] ⟶ Y, (upper A).ι ≫ g = f := by
  let _ : HasLiftingProperty (upper A).ι (terminal.from Y) :=
    upper_anodyne A _ (by rwa [← HomotopicalAlgebra.fibration_iff])
  let sq : CommSq f (upper A).ι (terminal.from Y) (terminal.from (X ⊗ Δ[1])) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- The chosen actual scalar open-box extension. -/
def fill {X Y : SSet.{u}} (A : X.Subcomplex) [SSet.KanComplex Y]
    (f : (upper A : SSet) ⟶ Y) : X ⊗ Δ[1] ⟶ Y :=
  (exists_fill A f).choose

/-- The actual extension retains the entire original box restriction, not just its vertices. -/
theorem fill_restrict {X Y : SSet.{u}} (A : X.Subcomplex) [SSet.KanComplex Y]
    (f : (upper A : SSet) ⟶ Y) : (upper A).ι ≫ fill A f = f :=
  (exists_fill A f).choose_spec

end CategoryTheory.CoherentRealization.OpenBox
