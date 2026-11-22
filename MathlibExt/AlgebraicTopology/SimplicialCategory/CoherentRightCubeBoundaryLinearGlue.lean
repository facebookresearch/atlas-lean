/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeBoundaryGlue

/-!
# Actual ordered-pair original right-cube boundary gluing

The same original subcomplex cover has its genuine ordered-pair
multicoequalizer. Only the literal agreements for distinct labels in
increasing order are needed. This retains the degree-zero empty boundary
and avoids assuming any unproved whole latching or coherence outcome.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CoherentRealization.RightCubeBoundaryLinearGlue
open RightCubeSupportBoundary RightCubeBoundaryGlue

/-- Glue actual whole omitted-support maps from their literal increasing-pair intersection agreements. -/
def glue (n : ℕ) (T : SSet.{u}) (k : ∀ i : Fin (n + 1), (missing.{u} n i : SSet.{u}) ⟶ T)
    (hk : ∀ (i j : Fin (n + 1)), i < j →
      SSet.Subcomplex.homOfLE (show missing.{u} n i ⊓ missing n j ≤ missing n i from inf_le_left) ≫ k i =
        SSet.Subcomplex.homOfLE (show missing.{u} n i ⊓ missing n j ≤ missing n j from inf_le_right) ≫ k j) :
    (boundary.{u} n : SSet.{u}) ⟶ T :=
  (cover n).isColimit'.desc
    (Multicofork.ofπ ((cover n).multispanIndex.toLinearOrder.map SSet.Subcomplex.toSSetFunctor) T k
      (fun p => hk p.1.1 p.1.2 p.2))

/-- The entire genuine ordered-pair boundary gluing retains each supplied whole original coface map. -/
theorem inclusion_glue (n : ℕ) (T : SSet.{u})
    (k : ∀ i : Fin (n + 1), (missing.{u} n i : SSet.{u}) ⟶ T)
    (hk : ∀ (i j : Fin (n + 1)), i < j →
      SSet.Subcomplex.homOfLE (show missing.{u} n i ⊓ missing n j ≤ missing n i from inf_le_left) ≫ k i =
        SSet.Subcomplex.homOfLE (show missing.{u} n i ⊓ missing n j ≤ missing n j from inf_le_right) ≫ k j)
    (i : Fin (n + 1)) :
    SSet.Subcomplex.homOfLE (missing_le_boundary n i) ≫ glue n T k hk = k i :=
  (cover n).isColimit'.fac _ (WalkingMultispan.right i)

end CategoryTheory.CoherentRealization.RightCubeBoundaryLinearGlue
