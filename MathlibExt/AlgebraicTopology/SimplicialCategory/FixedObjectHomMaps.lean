/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomLaws

/-!
# Whole original Hom maps in the fixed-object category

Original endpoints are transported only through the actual label
equalities. A family of Hom maps preserving the original identity and
composition constructs a genuine fixed-object enriched functor, and
the whole enriched functor is determined by that family.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u}

/-- The actual original Hom isomorphism induced only by its individual endpoint label equalities. -/
def originalHomIso (C : FixedObjects O) (a b : C.val) :
    (a ⟶[SSet.{u}] b) ≅ hom C (label C a) (label C b) :=
  eqToIso (by change _ = (vertex C (label C a) ⟶[SSet.{u}] vertex C (label C b))
              rw [vertex_label, vertex_label])

/-- Label transport retains the entire original identity morphism. -/
theorem identity_originalHomIso (C : FixedObjects O) (a : C.val) :
    eId SSet.{u} a ≫ (originalHomIso C a a).hom = identityMap C (label C a) :=
  identity_eqToHom C.val (vertex_label C a).symm

/-- Label transport retains the entire original composition at all three individual endpoints. -/
theorem composition_originalHomIso (C : FixedObjects O) (a b c : C.val) :
    eComp SSet.{u} a b c ≫ (originalHomIso C a c).hom =
      ((originalHomIso C a b).hom ⊗ₘ (originalHomIso C b c).hom) ≫
        compositionMap C (label C a) (label C b) (label C c) :=
  composition_eqToHom C.val (vertex_label C a).symm
    (vertex_label C b).symm (vertex_label C c).symm

/-- Construct the actual fixed-object enriched map from its whole identity- and
composition-preserving Hom maps. -/
def ofHomMaps {C D : FixedObjects O} (m : ∀ x y : O, hom C x y ⟶ hom D x y)
    (hi : ∀ x, identityMap C x ≫ m x x = identityMap D x)
    (hc : ∀ x y z, compositionMap C x y z ≫ m x z =
      (m x y ⊗ₘ m y z) ≫ compositionMap D x y z) : C ⟶ D := by
  let F : C.val ⟶ D.val := {
    obj a := vertex D (label C a)
    map a b := (originalHomIso C a b).hom ≫ m (label C a) (label C b)
    map_id a := by
      change eId SSet.{u} a ≫ ((originalHomIso C a a).hom ≫ m (label C a) (label C a)) =
        identityMap D (label C a)
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ m (label C a) (label C a))
          (identity_originalHomIso C a)).trans (hi (label C a)))
    map_comp a b c := by
      change eComp SSet.{u} a b c ≫
          ((originalHomIso C a c).hom ≫ m (label C a) (label C c)) =
        (((originalHomIso C a b).hom ≫ m (label C a) (label C b)) ⊗ₘ
          ((originalHomIso C b c).hom ≫ m (label C b) (label C c))) ≫
            compositionMap D (label C a) (label C b) (label C c)
      rw [← Category.assoc, composition_originalHomIso, Category.assoc,
        hc (label C a) (label C b) (label C c), ← Category.assoc,
        ← tensorHom_comp_tensorHom] }
  refine ⟨F, ?_⟩
  apply IsHomLift.of_fac' forgetObjects (𝟙 O) F C.property D.property
  ext a
  rfl

/-- The constructed enriched map carries the same individual original object label. -/
@[simp]
theorem ofHomMaps_obj {C D : FixedObjects O} (m : ∀ x y : O, hom C x y ⟶ hom D x y)
    (hi : ∀ x, identityMap C x ≫ m x x = identityMap D x)
    (hc : ∀ x y z, compositionMap C x y z ≫ m x z =
      (m x y ⊗ₘ m y z) ≫ compositionMap D x y z) (a : C.val) :
    (ofHomMaps m hi hc).val.obj a = vertex D (label C a) := rfl

private theorem family_cast {C D : FixedObjects O} (m : ∀ x y : O, hom C x y ⟶ hom D x y)
    {x y x' y' : O} (hx : x = x') (hy : y = y') :
    eqToHom (by rw [hx, hy] : hom C x y = hom C x' y') ≫ m x' y' =
      m x y ≫ eqToHom (by rw [hx, hy] : hom D x y = hom D x' y') := by
  cases hx
  cases hy
  simp

/-- Evaluation reads back the exact supplied whole Hom map at every original ordered pair. -/
@[simp]
theorem homMap_ofHomMaps {C D : FixedObjects O} (m : ∀ x y : O, hom C x y ⟶ hom D x y)
    (hi : ∀ x, identityMap C x ≫ m x x = identityMap D x)
    (hc : ∀ x y z, compositionMap C x y z ≫ m x z =
      (m x y ⊗ₘ m y z) ≫ compositionMap D x y z) (x y : O) :
    homMap (ofHomMaps m hi hc) x y = m x y := by
  have h := family_cast m (label_vertex C x).symm (label_vertex C y).symm
  have h' := congrArg (fun k => k ≫ eqToHom
    (by rw [label_vertex, label_vertex] :
      hom D (label C (vertex C x)) (label C (vertex C y)) = hom D x y)) h
  change eqToHom (by rw [label_vertex, label_vertex] :
      hom C x y = hom C (label C (vertex C x)) (label C (vertex C y))) ≫
    m (label C (vertex C x)) (label C (vertex C y)) ≫
      eqToHom (by rw [label_vertex, label_vertex] :
        hom D (label C (vertex C x)) (label C (vertex C y)) = hom D x y) = m x y
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using h'

/-- Every genuine fixed-object map is determined by its full original Hom maps. -/
theorem homMaps_ext {C D : FixedObjects O} {F G : C ⟶ D}
    (h : ∀ x y : O, homMap F x y = homMap G x y) : F = G := by
  apply Functor.Fiber.hom_ext
  have ho : ∀ a : C.val, F.val.obj a = G.val.obj a := by
    intro a
    obtain ⟨x, hx⟩ := (verticesEquiv C).surjective a
    change vertex C x = a at hx
    subst a
    exact (map_vertex F x).trans (map_vertex G x).symm
  refine EnrichedFunctor.ext SSet.{u} (F := F.val) (G := G.val) ho ?_
  intro a b
  obtain ⟨x, hx⟩ := (verticesEquiv C).surjective a
  obtain ⟨y, hy⟩ := (verticesEquiv C).surjective b
  change vertex C x = a at hx
  change vertex C y = b at hy
  subst a
  subst b
  apply (cancel_mono (eqToHom (by rw [map_vertex G x, map_vertex G y] :
    (G.val.obj (vertex C x) ⟶[SSet.{u}] G.val.obj (vertex C y)) = hom D x y))).1
  simpa only [homMap, Category.assoc, eqToHom_trans] using h x y

end CategoryTheory.SimplicialEnrichment.FixedObjects
