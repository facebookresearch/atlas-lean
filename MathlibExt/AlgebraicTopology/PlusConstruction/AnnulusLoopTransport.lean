/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.AnnulusLoopClasses
public import MathlibExt.AlgebraicTopology.PlusConstruction.CellCollarRetractionNormalization
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality

/-!
# Retraction of the actual transported annular loop

The existing outer-region deformation supplies the actual radial basepoint
path. Full-collar normalization makes its original-space retraction the
constant path at the original basepoint. Naturality of the existing End
conjugation therefore identifies the retraction of the same transported
annular perimeter with its same original subgroup element.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology Topology.CWComplex
open scoped unitInterval

universe u

namespace AlgebraicTopology.LoopCellAttachment

variable (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x))

/-- The actual retraction of the included original basepoint is that original basepoint. -/
theorem retraction_includedBasepoint :
    CellCollarDeformation.retractionU X 1 (attachingMap X x P)
        (CellCollarDeformation.inclusionU X 1 (attachingMap X x P) x) = x := by
  let i := CellCollarDeformation.inclusionU X 1 (attachingMap X x P)
  let r := CellCollarDeformation.retractionU X 1 (attachingMap X x P)
  have h : (i ≫ r) x = x :=
    ConcreteCategory.congr_hom
      (CellCollarDeformation.inclusionU_retractionU X 1 (attachingMap X x P)) x
  exact (TopCat.comp_app i r x).symm.trans h

/-- At every time, the actual radial basepoint path retracts to the same original x. -/
theorem outerBasepointPath_retraction (p : P) (t : I) :
    CellCollarDeformation.retractionU X 1 (attachingMap X x P)
        (outerBasepointPath X x P p t) = x := by
  rw [outerBasepointPath_apply]
  exact (CellCollarDeformation.retractionU_deformationU X 1 (attachingMap X x P)
    t (outerBasepoint X x P p)).trans (retraction_outerBasepoint X x P p)

/-- The same mapped radial path, with its proved original endpoints, is the constant path. -/
theorem outerBasepointPath_map_retraction (p : P) :
    ((outerBasepointPath X x P p).map
        (CellCollarDeformation.retractionU X 1 (attachingMap X x P)).hom.continuous).cast
        (retraction_outerBasepoint X x P p).symm
        (retraction_includedBasepoint X x P).symm = Path.refl x := by
  apply Path.ext
  funext t
  change CellCollarDeformation.retractionU X 1 (attachingMap X x P)
    (outerBasepointPath X x P p t) = x
  exact outerBasepointPath_retraction X x P p t

/-- Its actual mapped path class is the identity after the same original endpoint casts. -/
theorem outerBasepointPath_map_retraction_class (p : P) :
    (Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.mk (outerBasepointPath X x P p))
        (CellCollarDeformation.retractionU X 1 (attachingMap X x P)).hom).cast
        (retraction_outerBasepoint X x P p).symm
        (retraction_includedBasepoint X x P).symm =
      Path.Homotopic.Quotient.refl x := by
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
    outerBasepointPath_map_retraction, Path.Homotopic.Quotient.mk_refl]

/-- Retraction of the actual transported annular perimeter is the SAME original p. -/
theorem retraction_transportedOuterPerimeterClass (p : P) :
    FundamentalGroup.mapOfEq
        (CellCollarDeformation.retractionU X 1 (attachingMap X x P)).hom
        (retraction_includedBasepoint X x P)
        (transportedOuterPerimeterClass X x P p) = p.val := by
  change FundamentalGroup.mapOfEq
      (CellCollarDeformation.retractionU X 1 (attachingMap X x P)).hom
      (retraction_includedBasepoint X x P)
      (FundamentalGroup.fundamentalGroupMulEquivOfPath (outerBasepointPath X x P p)
        (outerPerimeterClass X x P p)) = p.val
  calc
    _ = FundamentalGroup.fundamentalGroupMulEquivOfPath
        (((outerBasepointPath X x P p).map
          (CellCollarDeformation.retractionU X 1 (attachingMap X x P)).hom.continuous).cast
          (retraction_outerBasepoint X x P p).symm
          (retraction_includedBasepoint X x P).symm)
        (FundamentalGroup.mapOfEq
          (CellCollarDeformation.retractionU X 1 (attachingMap X x P)).hom
          (retraction_outerBasepoint X x P p) (outerPerimeterClass X x P p)) :=
      FundamentalGroup.mapOfEq_fundamentalGroupMulEquivOfPath
        (CellCollarDeformation.retractionU X 1 (attachingMap X x P)).hom
        (retraction_outerBasepoint X x P p) (retraction_includedBasepoint X x P)
        (outerBasepointPath X x P p) (outerPerimeterClass X x P p)
    _ = FundamentalGroup.mapOfEq
        (CellCollarDeformation.retractionU X 1 (attachingMap X x P)).hom
        (retraction_outerBasepoint X x P p) (outerPerimeterClass X x P p) := by
      rw [outerBasepointPath_map_retraction,
        FundamentalGroup.fundamentalGroupMulEquivOfPath_refl]
    _ = p.val := retraction_outerPerimeterClass X x P p

end AlgebraicTopology.LoopCellAttachment

end

end
