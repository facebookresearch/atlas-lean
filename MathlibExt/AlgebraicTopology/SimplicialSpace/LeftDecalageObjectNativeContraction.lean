/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialObjectHomotopyDiagonalEndpoints
import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectIdentitySection

/-!
# The actual original extra-degeneracy contraction on the path diagonal

The whole fixed-object extra degeneracy supplies a combinatorial homotopy
from the original augmentation followed by its original section to the
identity. Its diagonal is the actual interval homotopy retaining both
original maps and the whole original homotopy faces.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The original whole fixed-object extra-degeneracy section. -/
def nativeSection (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (SimplicialObject.const SSet.{u}).obj (Δ[0] : SSet.{u}) ⟶ diagram W x :=
  (extraDegeneracy W x).section_

/-- The original whole augmentation-section roundtrip on the complete fixed-object path diagram. -/
def nativeRetraction (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    diagram W x ⟶ diagram W x := toPoint W x ≫ nativeSection W x

/-- The original extra degeneracy gives the actual diagonal contraction interval homotopy. -/
def nativeDiagonalContraction (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.Homotopy (SSet.simplicialDiagonalFunctor.map (nativeRetraction W x))
      (𝟙 (SSet.simplicialDiagonalFunctor.obj (diagram W x))) := by
  have h := (extraDegeneracy W x).homotopy.toDiagonalHomotopy
  change SSet.Homotopy (SSet.simplicialDiagonalFunctor.map (nativeRetraction W x))
    (SSet.simplicialDiagonalFunctor.map (𝟙 (diagram W x))) at h
  rw [SSet.simplicialDiagonalFunctor.map_id] at h
  exact h

/-- The actual original section at zero degree is the same retained identity section. -/
theorem nativeSection_zero (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (nativeSection W x).app (op (SimplexCategory.mk 0)) = sectionZero W x := by
  change (extraDegeneracy W x).section_.app (op (SimplexCategory.mk 0)) = sectionZero W x
  rw [(extraDegeneracy W x).section_app_op_mk_zero, sectionZero_eq_extraDegeneracy_section]

end SimplicialSpace.LeftDecalageObject
