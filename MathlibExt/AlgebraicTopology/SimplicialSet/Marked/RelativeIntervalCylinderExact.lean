/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeIntervalCylinder
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Exactness of the original source-projection interval cylinder

The original marked endpoint pullbacks transfer through the faithful
slice forgetful functor. Its preserved coproduct comparison keeps the
same whole marked boundary map and proves native monicity. The original
interval adjunction gives colimit preservation. These are exactness
proofs on the actual fixed-base cylinder, not model hypotheses.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked

/-- The complete original relative endpoint keeps exactly the old marked endpoint map. -/
theorem relativeIntervalCylinder_endpoint_left (Z : Marked.{u}) (X : Over Z) (ε : Fin 2) :
    (((relativeIntervalCylinder Z).app X).endpoint ε).left = intervalCylinderEndpoint X.left ε := by
  fin_cases ε <;> rfl

/-- The preserved original coproduct comparison identifies the entire relative marked boundary with the old
  native boundary. -/
theorem relativeIntervalCylinder_boundary_comparison (Z : Marked.{u}) (X : Over Z) :
    (PreservesColimitPair.iso (Over.forget Z) X X).hom ≫ ((relativeIntervalCylinder Z).app X).i.left =
      (intervalCylinder.{u}.app X.left).i := by
  apply coprod.hom_ext
  · have he : (coprod.inl : X.left ⟶ X.left ⨿ X.left) ≫
        (PreservesColimitPair.iso (Over.forget Z) X X).hom = (coprod.inl : X ⟶ X ⨿ X).left := by
      rw [PreservesColimitPair.iso_hom]
      exact coprod.inl_desc _ _
    have hi : (coprod.inl : X ⟶ X ⨿ X).left ≫ ((relativeIntervalCylinder Z).app X).i.left =
        (intervalCylinderEndpoint X.left 0) := congrArg Over.Hom.left (Precylinder.inl_i _)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ _) he).trans (hi.trans (Precylinder.inl_i (intervalCylinder.{u}.app X.left)).symm))
  · have he : (coprod.inr : X.left ⟶ X.left ⨿ X.left) ≫
        (PreservesColimitPair.iso (Over.forget Z) X X).hom = (coprod.inr : X ⟶ X ⨿ X).left := by
      rw [PreservesColimitPair.iso_hom]
      exact coprod.inr_desc _ _
    have hi : (coprod.inr : X ⟶ X ⨿ X).left ≫ ((relativeIntervalCylinder Z).app X).i.left =
        (intervalCylinderEndpoint X.left 1) := congrArg Over.Hom.left (Precylinder.inr_i _)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ _) he).trans (hi.trans (Precylinder.inr_i (intervalCylinder.{u}.app X.left)).symm))

/-- The original relative marked boundary is monic on its whole original slice carrier. -/
theorem relativeIntervalCylinder_boundary_mono (Z : Marked.{u}) (X : Over Z) :
    Mono ((relativeIntervalCylinder Z).app X).i := by
  let _ : intervalCylinder.{u}.IsExact.{u} := intervalCylinder_isExact
  let _ : Mono (intervalCylinder.{u}.app X.left).i := Precylinder.IsExact.mono_boundary X.left
  let e := PreservesColimitPair.iso (Over.forget Z) X X
  let f := ((relativeIntervalCylinder Z).app X).i.left
  let a : Arrow.mk (intervalCylinder.{u}.app X.left).i ≅ Arrow.mk f :=
    Arrow.isoMk e (Iso.refl _) ((relativeIntervalCylinder_boundary_comparison Z X).trans (Category.comp_id _).symm)
  let _ : Mono f := ((MorphismProperty.monomorphisms Marked.{u}).arrow_iso_iff a).mp (inferInstance : Mono
    (intervalCylinder.{u}.app X.left).i)
  exact Over.mono_of_mono_left _

/-- The original fixed-base cylinder is genuinely exact at the unchanged original value universe. -/
theorem relativeIntervalCylinder_isExact (Z : Marked.{u}) : (relativeIntervalCylinder Z).IsExact.{u} := by
  let _ : Functor.PreservesMonomorphisms (relativeIntervalCylinder Z).I :=
    ⟨fun {X Y} i hi => by
      let _ : Mono i := hi
      let _ : Mono i.left := Over.mono_left_of_mono i
      let _ : Mono ((relativeIntervalCylinder Z).I.map i).left := intervalCylinder_map_mono i.left
      exact Over.mono_of_mono_left _⟩
  let _ : PreservesColimitsOfSize.{u, u} (relativeIntervalCylinder Z).I := relativeIntervalCylinder_preservesColimits Z
  refine { mono_boundary := relativeIntervalCylinder_boundary_mono Z, endpoint_isPullback := ?_ }
  intro X Y i _ ε
  let _ : Mono i.left := Over.mono_left_of_mono i
  have h := intervalCylinderEndpoint_isPullback i.left ε
  have hmap : IsPullback ((Over.forget Z).map i)
      ((Over.forget Z).map (((relativeIntervalCylinder Z).app X).endpoint ε))
      ((Over.forget Z).map (((relativeIntervalCylinder Z).app Y).endpoint ε))
      ((Over.forget Z).map ((relativeIntervalCylinder Z).I.map i)) := by
    change IsPullback i.left
      ((((relativeIntervalCylinder Z).app X).endpoint ε).left)
      ((((relativeIntervalCylinder Z).app Y).endpoint ε).left)
      (((relativeIntervalCylinder Z).I.map i).left)
    rw [relativeIntervalCylinder_endpoint_left, relativeIntervalCylinder_endpoint_left]
    exact h
  exact IsPullback.of_map (Over.forget Z) ((relativeIntervalCylinder Z).endpoint_naturality i ε) hmap

end SSet.Marked
