/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# Enriched functors under monoidal change of base

The same original enriched functor gives a functor after transporting each
Hom through a lax monoidal functor. Objects remain unchanged and local Hom
maps are their literal images. Identity and composition are derived from the
original enriched functor laws and the same monoidal tensorator.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe uV vV uW vW uC uD uE

open CategoryTheory MonoidalCategory

namespace CategoryTheory.EnrichedFunctor

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {W : Type uW} [Category.{vW} W] [MonoidalCategory W]
  (Q : V ⥤ W) [Q.LaxMonoidal]
  {C : Type uC} [EnrichedCategory V C] {D : Type uD} [EnrichedCategory V D]
  {E : Type uE} [EnrichedCategory V E]

set_option backward.isDefEq.respectTransparency false in
/-- Transport the literal original objects and Hom maps through the same monoidal functor. -/
def transportBase (F : EnrichedFunctor V C D) :
    EnrichedFunctor W (TransportEnrichment Q C) (TransportEnrichment Q D) where
  obj x := F.obj x
  map x y := Q.map (F.map x y)
  map_id x := by
    change (Functor.LaxMonoidal.ε Q ≫ Q.map (eId (C := C) V x)) ≫ Q.map (F.map x x) =
      Functor.LaxMonoidal.ε Q ≫ Q.map (eId (C := D) V (F.obj x))
    rw [Category.assoc, ← Q.map_comp, F.map_id]
  map_comp x y z := by
    change (Functor.LaxMonoidal.μ Q _ _ ≫ Q.map (eComp (C := C) V x y z)) ≫ Q.map (F.map x z) =
      (Q.map (F.map x y) ⊗ₘ Q.map (F.map y z)) ≫
        (Functor.LaxMonoidal.μ Q _ _ ≫ Q.map (eComp (C := D) V (F.obj x) (F.obj y) (F.obj z)))
    rw [Category.assoc, ← Q.map_comp, F.map_comp, Q.map_comp,
      ← Functor.LaxMonoidal.μ_natural_assoc]

@[simp]
theorem transportBase_obj (F : EnrichedFunctor V C D) (x : C) :
    (transportBase Q F).obj x = F.obj x := rfl

@[simp]
theorem transportBase_map (F : EnrichedFunctor V C D) (x y : C) :
    (transportBase Q F).map x y = Q.map (F.map x y) := rfl

/-- The whole transported enriched identity is the original identity functor. -/
theorem transportBase_id : transportBase Q (EnrichedFunctor.id V C) =
    EnrichedFunctor.id W (TransportEnrichment Q C) := by
  apply EnrichedFunctor.ext W
    (F := transportBase Q (EnrichedFunctor.id V C))
    (G := EnrichedFunctor.id W (TransportEnrichment Q C)) (fun _ => rfl)
  intro x y
  change Q.map (𝟙 _) ≫ eqToHom _ = 𝟙 _
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Monoidal change of base retains composition of the same enriched Hom maps. -/
theorem transportBase_comp (F : EnrichedFunctor V C D) (G : EnrichedFunctor V D E) :
    transportBase Q (EnrichedFunctor.comp V F G) =
      EnrichedFunctor.comp W (transportBase Q F) (transportBase Q G) := by
  apply EnrichedFunctor.ext W
    (F := transportBase Q (EnrichedFunctor.comp V F G))
    (G := EnrichedFunctor.comp W (transportBase Q F) (transportBase Q G)) (fun _ => rfl)
  intro x y
  change Q.map (F.map x y ≫ G.map (F.obj x) (F.obj y)) ≫ eqToHom _ =
    Q.map (F.map x y) ≫ Q.map (G.map (F.obj x) (F.obj y))
  have he : ∀ h : Q.obj (G.obj (F.obj x) ⟶[V] G.obj (F.obj y)) =
      Q.obj (G.obj (F.obj x) ⟶[V] G.obj (F.obj y)), eqToHom h = 𝟙 _ := by
    intro h
    rfl
  rw [he, Category.comp_id, Q.map_comp]

end CategoryTheory.EnrichedFunctor
