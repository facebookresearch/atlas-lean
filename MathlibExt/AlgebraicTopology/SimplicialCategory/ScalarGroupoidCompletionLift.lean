/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionFunctor

/-!
# Genuine full universal lifts from canonical scalar groupoid completion

A target whose SAME canonical scalar categories are actual groupoids
admits the native full degreewise completion lift. Its all-degree Hom
maps commute with every original ordinal operator, using native lift
uniqueness and the SAME canonical source naturality. The original full
unit followed by the actual enriched lift is exactly the supplied map.
This is an ordinary enriched universal property; no weak outcome follows
without a separate genuine homotopical group-completion theorem.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion

variable {C D : Carrier.{u}} [∀ q, IsGroupoid (SSet.ScalarObject D q)]

/-- The actual native full completion lift into the SAME original scalar-groupoid target. -/
def scalarLift (F : C ⟶ D) (q : SimplexCategoryᵒᵖ) : category C q ⥤ SSet.ScalarObject D q := by
  let _ : Groupoid (SSet.ScalarObject D q) := Groupoid.ofIsGroupoid
  exact FreeGroupoid.lift (SSet.scalarFunctor F q)

/-- The SAME native scalar lift retains the actual supplied original object image. -/
theorem scalarLift_vertex (F : C ⟶ D) (q : SimplexCategoryᵒᵖ) (x : C) :
    (scalarLift F q).obj (vertex C q x) = SSet.ScalarObject.mk (Δ := q) (F.obj x) := rfl

/-- The native full scalar lift commutes with each SAME original canonical ordinal operator. -/
theorem scalarLift_operator (F : C ⟶ D) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) :
    operator C f ⋙ scalarLift F r = scalarLift F q ⋙ SSet.scalarOperator (C := D) f := by
  let _ : Groupoid (SSet.ScalarObject D q) := Groupoid.ofIsGroupoid
  let _ : Groupoid (SSet.ScalarObject D r) := Groupoid.ofIsGroupoid
  exact (FreeGroupoid.map_comp_lift (SSet.scalarOperator (C := C) f) (SSet.scalarFunctor F r)).trans
    ((congrArg FreeGroupoid.lift (SSet.scalarFunctor_operator F f)).trans
      (FreeGroupoid.lift_comp (SSet.scalarFunctor F q) (SSet.scalarOperator (C := D) f)))

/-- The actual full enriched lift Hom map uses every SAME native degreewise completion arrow. -/
def liftHom (F : C ⟶ D) (x y : C) : hom C x y ⟶ (F.obj x ⟶[SSet.{u}] F.obj y) where
  app q := ↾fun a => (scalarLift F q).map a
  naturality q r f := by
    ext a
    exact eq_of_heq (Functor.hcongr_hom (scalarLift_operator F f) a)

/-- The supplied original enriched functor has an actual whole completion lift with the SAME
original object map. -/
def lift (F : C ⟶ D) : object C ⟶ D where
  obj := F.obj
  map := liftHom F
  map_id x := by
    ext q a
    exact (scalarLift F q).map_id (vertex C q x)
  map_comp x y z := by
    ext q a
    exact (scalarLift F q).map_comp a.1 a.2

/-- Every SAME original Hom simplex reads back through its native full unit and scalar lift. -/
theorem unitHom_liftHom (F : C ⟶ D) (x y : C) : unitHom C x y ≫ liftHom F x y = F.map x y := by
  ext q a
  let _ : Groupoid (SSet.ScalarObject D q) := Groupoid.ofIsGroupoid
  exact FreeGroupoid.lift_map_homMk (SSet.scalarFunctor F q)
    (X := SSet.ScalarObject.mk (Δ := q) x) (Y := SSet.ScalarObject.mk (Δ := q) y) a

/-- The SAME actual original unit followed by its genuine whole completion lift is exactly
the supplied enriched
functor. -/
theorem unit_lift (F : C ⟶ D) : unit C ≫ lift F = F := by
  apply EnrichedFunctor.ext SSet.{u} (F := unit C ≫ lift F) (G := F) (fun _ => rfl)
  intro x y
  change (unitHom C x y ≫ liftHom F x y) ≫ eqToHom _ = F.map x y
  exact (congrArg (fun m => m ≫ eqToHom (rfl : (F.obj x ⟶[SSet.{u}] F.obj y) =
    (F.obj x ⟶[SSet.{u}] F.obj y))) (unitHom_liftHom F x y)).trans (Category.comp_id _)

/-- Every actual full lifted Hom uses the SAME native scalar completion arrow map in each degree. -/
theorem lift_apply (F : C ⟶ D) (q : SimplexCategoryᵒᵖ) (x y : C) (a : (hom C x y).obj q) :
    ((lift F).map x y).app q a = (scalarLift F q).map a := rfl

end CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
