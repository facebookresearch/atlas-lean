/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFreeQuiver
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeSingleHomAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel

/-!
# Same original scalar maps in the single-Hom generating quiver

The map is the supplied scalar map at the exact original ordered pair
and the initial-object isomorphism elsewhere. Its whole free map is
proved equal to the existing free single-Hom functor map. Loop pairs
and nullary scalar inputs use these same original constructions.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialQuiver.SingleHom

variable {O : Type u} (x y : O)

/-- The same supplied scalar map at its original pair, with actual initial generating Homs elsewhere. -/
def quiverMap {X Y : SSet.{u}} (f : X ⟶ Y) (a b : O) : (quiver x y X).Hom a b ⟶ (quiver x y Y).Hom a b := by
  classical
  by_cases h : a = x ∧ b = y
  · rcases h with ⟨ha, hb⟩
    subst a
    subst b
    exact eqToHom (quiver_at x y X) ≫ f ≫ eqToHom (quiver_at x y Y).symm
  · exact eqToHom (quiver_other x y X a b h) ≫ eqToHom (quiver_other x y Y a b h).symm

/-- The specified original quiver map retains the actual scalar map under the two literal Hom equalities. -/
theorem quiverMap_at {X Y : SSet.{u}} (f : X ⟶ Y) :
    quiverMap x y f x y = eqToHom (quiver_at x y X) ≫ f ≫ eqToHom (quiver_at x y Y).symm := by
  classical
  simp [quiverMap]

/-- Every other original pair has the actual initial-object comparison map. -/
theorem quiverMap_other {X Y : SSet.{u}} (f : X ⟶ Y) (a b : O) (h : ¬(a = x ∧ b = y)) :
    quiverMap x y f a b = eqToHom (quiver_other x y X a b h) ≫ eqToHom (quiver_other x y Y a b h).symm := by
  classical
  simp only [quiverMap, dite_eq_right h]

/-- The actual free map of that quiver is the whole original free single-Hom functor map. -/
theorem free_quiverMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    SimplicialEnrichment.FixedObjects.FreeQuiver.map (quiverMap x y f) =
      (SimplicialEnrichment.FixedObjects.FreeSingleHom.functor x y).map f := by
  open SimplicialEnrichment.FixedObjects in
  apply (FreeSingleHom.homEquiv x y X (FreeSingleHom.object x y Y)).injective
  change FreeSingleHom.generator x y X ≫ homMap (FreeQuiver.map (quiverMap x y f)) x y =
    FreeSingleHom.generator x y X ≫ homMap (FreeSingleHom.map x y f) x y
  rw [FreeSingleHom.generator_map]
  change (eqToHom (quiver_at x y X).symm ≫ FreeQuiver.generator (quiver x y X) x y) ≫
    homMap (FreeQuiver.map (quiverMap x y f)) x y = f ≫ FreeSingleHom.generator x y Y
  rw [Category.assoc, FreeQuiver.generator_map, quiverMap_at]
  change (eqToIso (quiver_at x y X)).inv ≫ (eqToIso (quiver_at x y X)).hom ≫ f ≫
    (eqToIso (quiver_at x y Y)).inv ≫ FreeQuiver.generator (quiver x y Y) x y =
      f ≫ (eqToIso (quiver_at x y Y)).inv ≫ FreeQuiver.generator (quiver x y Y) x y
  simp only [Iso.inv_hom_id_assoc]

/-- Actual scalar anodyne maps give anodyne maps at every original generating pair, including loops. -/
theorem quiverMap_anodyne {X Y : SSet.{u}} (f : X ⟶ Y) (hf : SSet.anodyneExtensions f) (a b : O) :
    SSet.anodyneExtensions (quiverMap x y f a b) := by
  classical
  by_cases h : a = x ∧ b = y
  · rcases h with ⟨ha, hb⟩
    subst a
    subst b
    rw [quiverMap_at]
    exact SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
      (SSet.anodyneExtensions.comp_mem _ _ hf (SSet.anodyneExtensions.of_isIso _))
  · rw [quiverMap_other x y f a b h]
    exact SSet.anodyneExtensions.of_isIso _

end CategoryTheory.SimplicialQuiver.SingleHom
