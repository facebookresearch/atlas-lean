/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelPushforwardAdjunction

/-! # Whole changing-object enriched maps with prescribed original label functions

The canonical reindexed target and its identity Hom projection retain
all original Hom maps. Its fixed-source maps are determined by their
whole projected functors. An actual object-function equation transports
the canonical fixed part, giving a genuine whole map with that boundary.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.CarrierLabelMaps
open FixedObjects CarrierReindexing

private theorem map_heq_of_eq {C D : Carrier.{u}} {F G : C ⟶ D}
    (h : F = G) (x y : C) : HEq (F.map x y) (G.map x y) := by
  cases h
  rfl

/-- The whole projected map has exactly its prescribed original object function. -/
theorem projected_obj {C D : Carrier.{u}} (a : C → D)
    (F : source C ⟶ object D a) (x : C) :
    (F.val ≫ toTarget D a).obj x = a x := by
  change a (F.val.obj x) = a x
  have h := map_vertex F x
  change F.val.obj x = x at h
  rw [h]

/-- Whole fixed-source maps into a reindexed target are determined by their same projected
functors. -/
theorem projection_injective {A : Type u} {C : FixedObjects A} {D : Carrier.{u}} (a : A → D) :
    Function.Injective (fun F : C ⟶ object D a => F.val ≫ toTarget D a) := by
  intro F G h
  rcases F with ⟨⟨fobj, fmap, fid, fcomp⟩, hf⟩
  rcases G with ⟨⟨gobj, gmap, gid, gcomp⟩, hg⟩
  have hoF : fobj = label C := funext fun x => by
    have hx := map_vertex (C := C) (D := object D a) ⟨⟨fobj, fmap, fid, fcomp⟩, hf⟩ (label C x)
    rw [vertex_label] at hx
    exact hx
  have hoG : gobj = label C := funext fun x => by
    have hx := map_vertex (C := C) (D := object D a) ⟨⟨gobj, gmap, gid, gcomp⟩, hg⟩ (label C x)
    rw [vertex_label] at hx
    exact hx
  subst fobj
  subst gobj
  apply Functor.Fiber.hom_ext
  refine EnrichedFunctor.ext SSet.{u} (C := C.val) (D := (object D a).val)
    (F := ⟨label C, fmap, fid, fcomp⟩)
    (G := ⟨label C, gmap, gid, gcomp⟩) (fun _ => rfl) ?_
  intro x y
  have hh := map_heq_of_eq h x y
  have hm : fmap x y ≫ 𝟙 _ = gmap x y ≫ 𝟙 _ := eq_of_heq hh
  simpa only [eqToHom_refl, Category.comp_id] using hm

/-- An actual equality of the prescribed object functions retains the complete projection. -/
theorem projection_transport {C D : Carrier.{u}} {a b : C → D} (h : a = b) :
    (eqToHom (congrArg (object D) h)).val ≫ toTarget D b = toTarget D a := by
  cases h
  change (𝟙 (object D a).val) ≫ toTarget D a = toTarget D a
  exact Category.id_comp _

/-- The actual whole functor is transported only through its proved original object-function
equation. -/
def ofObjectEquation {C D : Carrier.{u}} (a : C → D) (F : C ⟶ D) (h : F.obj = a) :
    source C ⟶ object D a :=
  fixedPart F ≫ eqToHom (congrArg (object D) h)

/-- The transported fixed part retains the same whole original enriched functor. -/
theorem ofObjectEquation_fac {C D : Carrier.{u}} (a : C → D) (F : C ⟶ D) (h : F.obj = a) :
    (ofObjectEquation a F h).val ≫ toTarget D a = F := by
  change ((fixedPart F).val ≫ (eqToHom (congrArg (object D) h)).val) ≫ toTarget D a = F
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (fixedPart F).val ≫ k) (projection_transport h)).trans
      (factorization F))

/-- Every fixed-source lift retaining that entire original functor is the same transported
fixed part. -/
theorem ofObjectEquation_unique {C D : Carrier.{u}} (a : C → D) (F : C ⟶ D)
    (h : F.obj = a) (G : source C ⟶ object D a)
    (hG : G.val ≫ toTarget D a = F) : G = ofObjectEquation a F h :=
  projection_injective a (hG.trans (ofObjectEquation_fac a F h).symm)

end CategoryTheory.SimplicialEnrichment.CarrierLabelMaps
