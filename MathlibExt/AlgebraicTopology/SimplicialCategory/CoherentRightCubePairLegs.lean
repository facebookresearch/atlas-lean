/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubePairFaces
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeCosimplicial

/-!
# Whole original coface legs of actual pair intersections

The genuine intersection isomorphism reads each original coface leg as
the same lower quotient operator. Both leg equations follow from their
actual ambient inclusions and whole cosimplicial composition, retaining
all supplied original labels and scalar cells.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubePairLegs
open RightCubePairFaces RightCubeFaceRangeIso RightCubeSupportBoundary
variable {n : ℕ}

/-- The entire original pair intersection leg into the first coface is its actual lower original quotient face map. -/
theorem left_leg (i j : Fin (n + 3)) (hij : i < j) :
    (pairIso.{u} i j hij).hom ≫ SSet.Subcomplex.homOfLE (show missing (n + 2) i ⊓ missing (n + 2) j ≤
      missing (n + 2) i from inf_le_left) =
      RightCubeCosimplicialMaps.map (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij))) ≫ (cofaceIso i).hom := by
  let e := pairIso.{u} i j hij
  let l := SSet.Subcomplex.homOfLE (show missing.{u} (n + 2) i ⊓ missing (n + 2) j ≤ missing (n + 2) i from inf_le_left)
  let f := RightCubeCosimplicialMaps.map.{u} (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij)))
  let d := (cofaceIso.{u} i).hom
  have hmap : RightCubeCosimplicialMaps.map.{u} (operator i j hij) = f ≫ RightCubeCosimplicialMaps.map
    (SimplexCategory.δ i) :=
    (RightCubeCosimplicial.diagram.{u}).map_comp _ _
  apply (cancel_mono (missing.{u} (n + 2) i).ι).1
  exact (Category.assoc e.hom l (missing (n + 2) i).ι).trans
    ((congrArg (fun h => e.hom ≫ h) (SSet.Subcomplex.homOfLE_ι inf_le_left)).trans
      ((pairIso_inclusion i j hij).trans
        (hmap.trans ((congrArg (fun h => f ≫ h) (cofaceIso_inclusion i).symm).trans
          (Category.assoc f d (missing (n + 2) i).ι).symm))))

/-- The entire original pair intersection leg into the second coface is its same alternate lower original
  quotient face map. -/
theorem right_leg (i j : Fin (n + 3)) (hij : i < j) :
    (pairIso.{u} i j hij).hom ≫ SSet.Subcomplex.homOfLE (show missing (n + 2) i ⊓ missing (n + 2) j ≤
      missing (n + 2) j from inf_le_right) =
      RightCubeCosimplicialMaps.map (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij))) ≫ (cofaceIso j).hom := by
  let e := pairIso.{u} i j hij
  let l := SSet.Subcomplex.homOfLE (show missing.{u} (n + 2) i ⊓ missing (n + 2) j ≤ missing (n + 2) j from
    inf_le_right)
  let f := RightCubeCosimplicialMaps.map.{u} (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij)))
  let d := (cofaceIso.{u} j).hom
  have hmap : RightCubeCosimplicialMaps.map.{u} (operator i j hij) = f ≫ RightCubeCosimplicialMaps.map
    (SimplexCategory.δ j) :=
    (congrArg (fun θ => RightCubeCosimplicialMaps.map.{u} θ) (operator_other i j hij)).trans
      ((RightCubeCosimplicial.diagram.{u}).map_comp _ _)
  apply (cancel_mono (missing.{u} (n + 2) j).ι).1
  exact (Category.assoc e.hom l (missing (n + 2) j).ι).trans
    ((congrArg (fun h => e.hom ≫ h) (SSet.Subcomplex.homOfLE_ι inf_le_right)).trans
      ((pairIso_inclusion i j hij).trans
        (hmap.trans ((congrArg (fun h => f ≫ h) (cofaceIso_inclusion j).symm).trans
          (Category.assoc f d (missing (n + 2) j).ι).symm))))

end CategoryTheory.CoherentRealization.RightCubePairLegs
