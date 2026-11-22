/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeSupportBoundary
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# Actual original right-cube boundary gluing over whole intersections

The original omitted-support subcomplexes have their literal pairwise
intersections and cover the actual proper-support boundary. The pinned
subcomplex multicoequalizer theorem therefore constructs genuine whole
boundary maps and proves their universal readbacks in every degree.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CoherentRealization.RightCubeBoundaryGlue
open RightCubeSupportBoundary

/-- The actual original omitted-support cover, with precisely its whole pair intersections. -/
theorem cover (n : ℕ) : SSet.Subcomplex.MulticoequalizerDiagram (boundary.{u} n)
    (missing n) (fun i j => missing n i ⊓ missing n j) where
  iSup_eq := (boundary_eq_iSup n).symm
  eq_inf _ _ := rfl

/-- Glue actual whole maps on the original omitted-support subcomplexes, with their supplied literal
  intersection agreements. -/
def glue (n : ℕ) (T : SSet.{u}) (k : ∀ i : Fin (n + 1), (missing.{u} n i : SSet.{u}) ⟶ T)
    (hk : ∀ i j, SSet.Subcomplex.homOfLE (show missing.{u} n i ⊓ missing n j ≤ missing n i from inf_le_left) ≫ k i =
      SSet.Subcomplex.homOfLE (show missing.{u} n i ⊓ missing n j ≤ missing n j from inf_le_right) ≫ k j) :
    (boundary.{u} n : SSet.{u}) ⟶ T :=
  (cover n).isColimit.desc (Multicofork.ofπ ((cover n).multispanIndex.map SSet.Subcomplex.toSSetFunctor) T k
    (fun p => hk p.1 p.2))

/-- The entire original boundary gluing recovers every supplied original omitted-support map. -/
theorem inclusion_glue (n : ℕ) (T : SSet.{u})
    (k : ∀ i : Fin (n + 1), (missing.{u} n i : SSet.{u}) ⟶ T)
    (hk : ∀ i j, SSet.Subcomplex.homOfLE (show missing.{u} n i ⊓ missing n j ≤ missing n i from inf_le_left) ≫ k i =
      SSet.Subcomplex.homOfLE (show missing.{u} n i ⊓ missing n j ≤ missing n j from inf_le_right) ≫ k j)
    (i : Fin (n + 1)) :
    SSet.Subcomplex.homOfLE (missing_le_boundary n i) ≫ glue n T k hk = k i :=
  (cover n).isColimit.fac _ (WalkingMultispan.right i)

/-- Whole original boundary maps are determined by all their actual omitted-support restrictions. -/
theorem hom_ext (n : ℕ) {T : SSet.{u}} {f g : (boundary.{u} n : SSet.{u}) ⟶ T}
    (h : ∀ i : Fin (n + 1), SSet.Subcomplex.homOfLE (missing_le_boundary n i) ≫ f =
      SSet.Subcomplex.homOfLE (missing_le_boundary n i) ≫ g) : f = g :=
  Multicofork.IsColimit.hom_ext (cover n).isColimit h

end CategoryTheory.CoherentRealization.RightCubeBoundaryGlue
