/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Combinatorics.Quiver.PathPositionFullLaws

/-!
# EVERY native original path-position word map

The original full position-word functor has exactly the SAME original
interval maps between all positions. Its native adjacent-arrow
construction and actual full interval identity/composition agree
as whole functors, without omission of any original ordinal arrow.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.Path
variable {V : Type u} [Quiver.{v} V] {x y : V}

/-- The SAME entire original word with the proved full original interval maps. -/
private def positionWordIntervals (p : Path x y) : Fin (p.length + 1) ⥤ Paths V where
  obj i := (positionVertex (V := V) p i : Paths V)
  map {i j} f := positionPath (V := V) p i j (leOfHom f)
  map_id i := positionPath_refl p i
  map_comp {i j k} f g := (positionPath_comp p i j k (leOfHom f) (leOfHom g)).symm

/-- Both entire native word constructions are the SAME original full position-word functor. -/
private lemma positionWord_eq_intervals (p : Path x y) : positionWord p = positionWordIntervals p := by
  refine ComposableArrows.ext (F := positionWord p) (G := positionWordIntervals p) (fun _ => rfl) ?_
  intro i hi
  change ComposableArrows.map' (positionWord p) i (i + 1) =
    eqToHom rfl ≫ positionPath (V := V) p
      (Fin.mk i (Nat.lt_trans hi (Nat.lt_succ_self _)))
      (Fin.mk (i + 1) (Nat.succ_lt_succ hi)) (Nat.le_succ i) ≫ eqToHom rfl
  rw [positionWord_map_succ, eqToHom_refl, Category.id_comp]
  change positionPath (V := V) p
      (Fin.mk i (Nat.lt_trans hi (Nat.lt_succ_self _)))
      (Fin.mk (i + 1) (Nat.succ_lt_succ hi)) (Nat.le_succ i) =
    (positionPath (V := V) p
      (Fin.mk i (Nat.lt_trans hi (Nat.lt_succ_self _)))
      (Fin.mk (i + 1) (Nat.succ_lt_succ hi)) (Nat.le_succ i)).comp Quiver.Path.nil
  exact (Quiver.Path.comp_nil _).symm

/-- EVERY full original ordinal path arrow is its SAME actual native interval subpath. -/
lemma positionWord_map (p : Path x y) {i j : Fin (p.length + 1)} (f : i ⟶ j) :
    (positionWord p).map f = positionPath (V := V) p i j (leOfHom f) := by
  exact eq_of_heq (Functor.hcongr_hom (positionWord_eq_intervals p) f)

end Quiver.Path
