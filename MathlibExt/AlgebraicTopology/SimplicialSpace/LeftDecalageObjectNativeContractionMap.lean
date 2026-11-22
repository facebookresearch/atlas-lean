/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeContractionEndpoints

/-!
# The point-endpoint contraction retains the original cylinder map

Displaying the original augmentation-section endpoint as its literal
constant map changes only its endpoint description. The complete original
native interval-cylinder map is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

private theorem endpoint_transport_h {K : SSet.{u}} {f g j : K ⟶ K}
    (h : f = g) (H : SSet.Homotopy f j) (ht : SSet.Homotopy f j = SSet.Homotopy g j) :
    (Eq.mp ht H).h = H.h := by
  cases h
  have he : ht = rfl := Subsingleton.elim _ _
  rw [he]
  rfl

/-- The actual point contraction has the same original complete interval-cylinder map. -/
theorem nativeDiagonalPointContraction_h (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (nativeDiagonalPointContraction W x).h = (nativeDiagonalContraction W x).h := by
  unfold nativeDiagonalPointContraction
  apply endpoint_transport_h (diagonal_nativeRetraction_eq_const W x)

end SimplicialSpace.LeftDecalageObject
