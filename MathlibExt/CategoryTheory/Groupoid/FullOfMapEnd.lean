/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Groupoid.Basic

/-!
# Fullness from the actual based endomorphism map

For a groupoid with connectors from a chosen source object, surjectivity
of the actual endomorphism map gives fullness on every original hom-set.
The target is an arbitrary category and the object/Hom universes are
independent. The lifted arrow uses the given connectors and the preimage
of its conjugated original endomorphism.
-/

noncomputable section

open CategoryTheory

universe uC vC uD vD

namespace CategoryTheory.Functor

/-- A based surjection and actual source connectors give a preimage of
every target arrow between original image objects. -/
public theorem full_of_surjective_mapEnd
    {C : Type uC} [Groupoid.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) (b : C) (β : ∀ c : C, b ⟶ c)
    (hs : Function.Surjective (F.mapEnd b)) : F.Full := by
  refine ⟨?_⟩
  intro c d q
  let w : End (F.obj b) := End.of (F.map (β c) ≫ q ≫ _root_.CategoryTheory.inv (F.map (β d)))
  obtain ⟨p, hp⟩ := hs w
  have hmap : F.map p.asHom = F.map (β c) ≫ q ≫ _root_.CategoryTheory.inv (F.map (β d)) :=
    congrArg (fun z : End (F.obj b) => z.asHom) hp
  refine ⟨_root_.CategoryTheory.inv (β c) ≫ p.asHom ≫ β d, ?_⟩
  simp only [Functor.map_comp, Functor.map_inv, hmap, Category.assoc,
    IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]

end CategoryTheory.Functor

end
