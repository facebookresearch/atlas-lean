/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubePairLegs

/-!
# Actual whole pair-face agreements on original cube intersections

A literal original pair-coface agreement gives the same whole agreement
on the actual intersection subcomplex through the proved coface inverse
maps. All isomorphisms and leg equations are the genuine constructed
ones; no intersection or coherence outcome is an input.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeIntersectionCompatibility
open RightCubePairFaces RightCubePairLegs RightCubeFaceRangeIso RightCubeSupportBoundary
variable {n : ℕ}

/-- A supplied original pair-face equation retains the whole same map on the actual original face intersection. -/
theorem ordered_pair (i j : Fin (n + 3)) (hij : i < j) {T : SSet.{u}}
    (f g : RightCubeRelations.object.{u} (n + 1) ⟶ T)
    (h : RightCubeCosimplicialMaps.map (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij))) ≫ f =
      RightCubeCosimplicialMaps.map (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij))) ≫ g) :
    SSet.Subcomplex.homOfLE (show missing.{u} (n + 2) i ⊓ missing (n + 2) j ≤ missing (n + 2) i from
      inf_le_left) ≫ (cofaceIso i).inv ≫ f =
      SSet.Subcomplex.homOfLE (show missing.{u} (n + 2) i ⊓ missing (n + 2) j ≤ missing (n + 2) j from
        inf_le_right) ≫ (cofaceIso j).inv ≫ g := by
  let e := pairIso.{u} i j hij
  let l := SSet.Subcomplex.homOfLE (show missing.{u} (n + 2) i ⊓ missing (n + 2) j ≤ missing (n + 2) i from inf_le_left)
  let r := SSet.Subcomplex.homOfLE (show missing.{u} (n + 2) i ⊓ missing (n + 2) j ≤ missing (n + 2) j from
    inf_le_right)
  have hL : e.hom ≫ l ≫ (cofaceIso i).inv ≫ f =
      RightCubeCosimplicialMaps.map (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij))) ≫ f := by
    calc
      _ = (e.hom ≫ l) ≫ ((cofaceIso i).inv ≫ f) := (Category.assoc _ _ _).symm
      _ = (RightCubeCosimplicialMaps.map (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij))) ≫ (cofaceIso i).hom) ≫
          ((cofaceIso i).inv ≫ f) := congrArg (fun k => k ≫ ((cofaceIso i).inv ≫ f)) (left_leg i j hij)
      _ = _ := (Category.assoc _ _ _).trans (congrArg (fun k =>
        RightCubeCosimplicialMaps.map (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij))) ≫ k) ((cofaceIso
          i).hom_inv_id_assoc f))
  have hR : e.hom ≫ r ≫ (cofaceIso j).inv ≫ g =
      RightCubeCosimplicialMaps.map (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij))) ≫ g := by
    calc
      _ = (e.hom ≫ r) ≫ ((cofaceIso j).inv ≫ g) := (Category.assoc _ _ _).symm
      _ = (RightCubeCosimplicialMaps.map (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij))) ≫ (cofaceIso j).hom) ≫
          ((cofaceIso j).inv ≫ g) := congrArg (fun k => k ≫ ((cofaceIso j).inv ≫ g)) (right_leg i j hij)
      _ = _ := (Category.assoc _ _ _).trans (congrArg (fun k =>
        RightCubeCosimplicialMaps.map (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij))) ≫ k)
          ((cofaceIso j).hom_inv_id_assoc g))
  apply (cancel_epi e.hom).1
  exact hL.trans (h.trans hR.symm)

end CategoryTheory.CoherentRealization.RightCubeIntersectionCompatibility
