/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.RealizedHornLeBoundaryCofibrations

/-!
# Boundary/horn right-class comparison in `TopCat`

This file is part of the KQ3 layer. The KQ3 provider
`TopCat.realizedHornInclusions_le_boundaryRLPLLP` places every realized horn
inclusion in the left class of the realized boundary inclusions. The
lifting-property Galois connection
(`MorphismProperty.le_llp_iff_le_rlp`) then reverses the inclusion on right
classes, giving `TopCat.realizedBoundaryInclusions.rlp` below
`TopCat.realizedHornInclusions.rlp`.

This is the order-theoretic half needed for the first model-structure
equality in every universe. It builds no weak-equivalence class and no model
structure.
-/

@[expose] public section

open CategoryTheory MorphismProperty

universe u

namespace TopCat

/-- Right-class comparison: boundary-RLP maps lift against horns. -/
theorem realizedBoundaryRLP_le_realizedHornRLP :
    (realizedBoundaryInclusions : MorphismProperty TopCat.{u}).rlp ≤
      (realizedHornInclusions : MorphismProperty TopCat.{u}).rlp :=
  (MorphismProperty.le_llp_iff_le_rlp _ _).mp
    realizedHornInclusions_le_boundaryRLPLLP

end TopCat
