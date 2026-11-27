/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.RealizedHornLeBoundaryCofibrations

/-!
# Comparison of realized boundary and horn right lifting classes

Every topological map with the right lifting property against realized simplicial
boundaries also has the right lifting property against realized simplicial horns.
This reverses the corresponding inclusion of generating left lifting classes.
-/

@[expose] public section

open CategoryTheory MorphismProperty

universe u

namespace TopCat

/--
The right lifting class of realized boundary inclusions is contained in the
right lifting class of realized horn inclusions.
-/
theorem realizedBoundaryRLP_le_realizedHornRLP :
    (realizedBoundaryInclusions : MorphismProperty TopCat.{u}).rlp ≤
      (realizedHornInclusions : MorphismProperty TopCat.{u}).rlp :=
  (MorphismProperty.le_llp_iff_le_rlp _ _).mp
    realizedHornInclusions_le_boundaryRLPLLP

end TopCat
