/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenQSZigzagNaturality
public import MathlibExt.KTheory.Exact.Quillen.KSpaceMap
public import MathlibExt.Topology.Homotopy.WeaklyPointedMap

/-!
# Continuous exact-functor maps on the Quillen loop-space carrier

The realized Quillen nerve map of an additive exact functor, equipped with
the canonical mapped-zero-to-target-zero path, is weakly pointed.  Applying
the generic weakly pointed loop construction gives a continuous map on the
Quillen K-space carrier.  Pointwise, it is definitionally the existing
conjugated `NQKSpaceMap`.

The strict grid-to-Q realization square also has a direct formulation on the
underlying continuous map of this weakly pointed endpoint.  No grid root
path or root compatibility is asserted.

This file constructs no strict weakly pointed or loop-map identity/composition
law, bundled homotopy, grid-zero coherence, final grid-loop naturality, weak
equivalence, direct Q/S equivalence, group comparison, or spectrum map.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : Functor C D) [F.Additive] [F.IsExact]

/-- The realized Quillen nerve map equipped with its canonical forward root
path from the mapped source zero to the target zero. -/
noncomputable def NQRealMapWeaklyPointed :
    ContinuousMap.WeaklyPointed
      (NQReal.basepoint C) (NQReal.basepoint D) where
  hom := (NQReal.map F).hom
  rootPath := NQKSpace.zeroComparisonRootPath C D F

/-- The underlying map of the weakly pointed Quillen realization map. -/
@[simp]
theorem NQRealMapWeaklyPointed_hom :
    (NQRealMapWeaklyPointed F).hom = (NQReal.map F).hom :=
  rfl

/-- The chosen root path is the existing mapped-zero-to-target-zero path in
the forward orientation. -/
@[simp]
theorem NQRealMapWeaklyPointed_rootPath :
    (NQRealMapWeaklyPointed F).rootPath =
      NQKSpace.zeroComparisonRootPath C D F :=
  rfl

/-- Continuous exact-functor map on the Quillen loop-space carrier. -/
noncomputable def NQKSpaceContinuousMap :
    C(NQKSpace C, NQKSpace D) :=
  (NQRealMapWeaklyPointed F).loopMap

/-- Pointwise, the continuous map is exactly the existing conjugated
Quillen K-space map. -/
@[simp]
theorem NQKSpaceContinuousMap_apply (gamma : NQKSpace C) :
    NQKSpaceContinuousMap F gamma = NQKSpaceMap C D F gamma :=
  rfl

/-- D2's strict grid-to-Q realization square expressed on the underlying
continuous map of the weakly pointed Quillen endpoint. -/
theorem quillenStageGridToNQ_realization_naturality_weak_hom :
    (quillenStageGridDiagonalRealMap F ≫
        SSet.toTop.map (quillenStageGridToNQ (C := D))).hom =
      (NQRealMapWeaklyPointed F).hom.comp
        (SSet.toTop.map (quillenStageGridToNQ (C := C))).hom := by
  change (quillenStageGridDiagonalRealMap F ≫
      SSet.toTop.map (quillenStageGridToNQ (C := D))).hom =
    (SSet.toTop.map (quillenStageGridToNQ (C := C)) ≫
      NQReal.map F).hom
  exact congrArg TopCat.Hom.hom
    (quillenStageGridToNQ_realization_naturality F)

end AlgebraicKTheory

end
