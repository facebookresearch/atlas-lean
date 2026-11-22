/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryOneMap

/-!
# Both original endpoint boundary maps are source natural

The canonical original one-boundary map retains both supplied original
vertices under every whole simplicial source map. The two literal face
readbacks prove the complete naturality square.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- Every original simplicial source map retains both SAME original endpoint boundary maps. -/
theorem boundaryOneMap_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌) :
    boundaryOneMap x y ≫ f = boundaryOneMap (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) := by
  apply boundary.hom_ext
  intro i
  fin_cases i
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ f) (boundary_ι_zero_boundaryOneMap x y)).trans
        ((const_comp y f).trans (boundary_ι_zero_boundaryOneMap (f.app (op ⦋0⦌) x)
          (f.app (op ⦋0⦌) y)).symm))
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ f) (boundary_ι_one_boundaryOneMap x y)).trans
        ((const_comp x f).trans (boundary_ι_one_boundaryOneMap (f.app (op ⦋0⦌) x)
          (f.app (op ⦋0⦌) y)).symm))

end SSet
