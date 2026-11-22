/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeLatchingDiagram
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeIntersectionCompatibility
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeEmptyOverlap

/-!
# Proved original intersection agreements of proper-face section families

Every actual proper-injection section family gives the same whole maps
on the original omitted-support intersections. Positive pair overlaps
use the actual shared original pair operator. The first positive degree
uses its genuine empty overlap. No additional coherence conclusion is
supplied as a hypothesis.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeLatchingCompatibility
open RightCubeSupportBoundary RightCubeFaceRangeIso RightCubePairFaces
variable {n : ℕ} {T : SSet.{u}}

/-- The actual whole original coface section read in its genuine omitted-support subcomplex. -/
def family (s : ∀ a : SimplicialObject.matchingIndex (n + 1), RightCubeRelations.object.{u} a.obj.right.unop.len ⟶ T)
    (i : Fin (n + 2)) : (missing.{u} (n + 1) i : SSet.{u}) ⟶ T :=
  (cofaceIso i).inv ≫ s (ProperFaceIndex.face n i)

/-- The actual proper-face section naturality proves the whole original increasing-pair intersection
  agreement, including the empty first overlap. -/
theorem ordered
    (s : ∀ a : SimplicialObject.matchingIndex (n + 1), RightCubeRelations.object.{u} a.obj.right.unop.len ⟶ T)
    (hs : ∀ {a b : SimplicialObject.matchingIndex (n + 1)} (g : a ⟶ b),
      RightCubeCosimplicialMaps.map g.hom.right.unop ≫ s a = s b)
    (i j : Fin (n + 2)) (hij : i < j) :
    SSet.Subcomplex.homOfLE (show missing.{u} (n + 1) i ⊓ missing (n + 1) j ≤ missing (n + 1) i from
      inf_le_left) ≫ family s i =
      SSet.Subcomplex.homOfLE (show missing.{u} (n + 1) i ⊓ missing (n + 1) j ≤ missing (n + 1) j from
        inf_le_right) ≫ family s j := by
  cases n with
  | zero => exact RightCubeEmptyOverlap.intersection_hom_ext i j (ne_of_lt hij) _ _
  | succ t =>
    let a : SimplicialObject.matchingIndex (t + 2) :=
      ⟨StructuredArrow.mk (operator i j hij).op,
        ⟨by
          change Mono (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij)) ≫ SimplexCategory.δ i)
          infer_instance,
          by change t < t + 2; omega⟩⟩
    let gi : ProperFaceIndex.face (t + 1) i ⟶ a := ProperFaceIndex.hom _ _
      (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij))) rfl
    let gj : ProperFaceIndex.face (t + 1) j ⟶ a := ProperFaceIndex.hom _ _
      (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij))) (operator_other i j hij).symm
    have h : RightCubeCosimplicialMaps.map (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij))) ≫
        s (ProperFaceIndex.face (t + 1) i) =
      RightCubeCosimplicialMaps.map (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij))) ≫
        s (ProperFaceIndex.face (t + 1) j) :=
      (hs gi).trans (hs gj).symm
    exact RightCubeIntersectionCompatibility.ordered_pair i j hij _ _ h

end CategoryTheory.CoherentRealization.RightCubeLatchingCompatibility
