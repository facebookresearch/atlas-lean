/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornRetraction

/-!
# Realized-horn retraction client

Direct application of `SSet.realizedHornRetract_ι` at `n = 1`, together with
the universe-polymorphic realized-horn locus import surface.
-/

@[expose] public section

namespace SSet

#check _root_.realizedHornHomeomorphHornLocus
#check _root_.hornRange_image_eq_locus_u

/-- Retraction law applied at `n = 1`, `k = 0`. -/
theorem realizedHornRetract_ι_one
    (x : SSet.toTop.obj (SSet.horn 1 ⟨0, by decide⟩)) :
    SSet.realizedHornRetract 1 ⟨0, by decide⟩ (by decide : 0 < 1)
      (SSet.toTop.map (SSet.horn 1 ⟨0, by decide⟩).ι x) = x :=
  SSet.realizedHornRetract_ι 1 ⟨0, by decide⟩ _ x

#print axioms SSet.realizedHornRetract_ι
#print axioms SSet.realizedHornRetract_ι_one

end SSet
