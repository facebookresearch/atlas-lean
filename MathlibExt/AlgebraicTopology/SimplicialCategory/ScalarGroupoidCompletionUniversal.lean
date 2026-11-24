/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionLift

/-!
# The genuine full enriched universal property of canonical completion

Every whole enriched map from the actual completion is recovered from
its SAME original unit restriction. The entire native scalar groupoid
functor has the same individual original objects and full Hom maps.
Native FreeGroupoid lift uniqueness proves recovery on every scalar
degree, yielding both full enriched inverse maps of the universal Hom
equivalence. No weak-map recognition theorem is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion

variable {C D : Carrier.{u}}

/-- The SAME original object is read from its actual native completion wrapper at one scalar
degree. -/
def originalVertex (q : SimplexCategoryᵒᵖ) (a : category C q) : C := a.as.as.obj

/-- Reading the original object after its actual native scalar completion image is literal. -/
theorem originalVertex_vertex (q : SimplexCategoryᵒᵖ) (x : C) :
    originalVertex (C := C) q (vertex C q x) = x := rfl

/-- Every actual native completion object retains its SAME original scalar object exactly. -/
theorem vertex_originalVertex (q : SimplexCategoryᵒᵖ) (a : category C q) :
    vertex C q (originalVertex (C := C) q a) = a := by
  cases a
  rfl

/-- The SAME entire enriched map acts on every actual native completed arrow in one original
scalar degree. -/
def nativeFunctor (H : object C ⟶ D) (q : SimplexCategoryᵒᵖ) :
    category C q ⥤ SSet.ScalarObject D q where
  obj a := ⟨H.obj (originalVertex (C := C) q a)⟩
  map {a b} h := (H.map (originalVertex (C := C) q a) (originalVertex (C := C) q b)).app q h
  map_id a := by
    exact congr($(H.map_id (originalVertex (C := C) q a)).app q PUnit.unit)
  map_comp {a b c} f g := by
    exact congr($(H.map_comp (originalVertex (C := C) q a)
      (originalVertex (C := C) q b) (originalVertex (C := C) q c)).app q (f, g))

/-- The actual native scalar restriction is exactly the SAME original full enriched unit
restriction. -/
theorem scalarUnit_nativeFunctor (H : object C ⟶ D) (q : SimplexCategoryᵒᵖ) :
    scalarUnit C q ⋙ nativeFunctor H q = SSet.scalarFunctor (unit C ≫ H) q := by
  apply Functor.hext (F := scalarUnit C q ⋙ nativeFunctor H q)
    (G := SSet.scalarFunctor (unit C ≫ H) q) (fun _ => rfl)
  intro x y a
  rfl

variable [∀ q, IsGroupoid (SSet.ScalarObject D q)]

/-- Every native completed arrow is recovered by the SAME full scalar lift of the original
unit restriction. -/
theorem scalarLift_restriction (H : object C ⟶ D) (q : SimplexCategoryᵒᵖ) :
    scalarLift (unit C ≫ H) q = nativeFunctor H q := by
  let _ : Groupoid (SSet.ScalarObject D q) := Groupoid.ofIsGroupoid
  exact (FreeGroupoid.lift_unique (SSet.scalarFunctor (unit C ≫ H) q)
    (nativeFunctor H q) (scalarUnit_nativeFunctor H q)).symm

/-- The genuine enriched lift of the SAME full original unit restriction recovers the entire
original completion map. -/
theorem lift_unit (H : object C ⟶ D) : lift (unit C ≫ H) = H := by
  apply EnrichedFunctor.ext SSet.{u} (F := lift (unit C ≫ H)) (G := H) (fun _ => rfl)
  intro x y
  change liftHom (unit C ≫ H) x y ≫ eqToHom _ = H.map x y
  have hm : liftHom (unit C ≫ H) x y = H.map x y := by
    ext q a
    exact eq_of_heq (Functor.hcongr_hom (scalarLift_restriction H q) a)
  exact (congrArg (fun m => m ≫ eqToHom (rfl : (H.obj x ⟶[SSet.{u}] H.obj y) =
    (H.obj x ⟶[SSet.{u}] H.obj y))) hm).trans (Category.comp_id _)

/-- Both genuine full inverse maps identify actual completion functors with SAME original
enriched functors into
scalar-groupoid targets. -/
def homEquiv : (object C ⟶ D) ≃ (C ⟶ D) where
  toFun H := unit C ≫ H
  invFun := lift
  left_inv := lift_unit
  right_inv := unit_lift

/-- The SAME actual original whole unit restriction detects equality of complete enriched
completion functors. -/
theorem unit_restriction_injective : Function.Injective (fun H : object C ⟶ D => unit C ≫ H) :=
  homEquiv.injective

end CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
