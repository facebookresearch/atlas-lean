/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectDiagonalSection

/-!
# The original native path contraction at its original constant basepoint

The complete original augmentation-section map equals the constant map at
the retained identity-edge diagonal basepoint. The original contraction
thus has that literal constant map and the literal identity as endpoints.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The whole original augmentation is the actual terminal map into the original zero simplex. -/
theorem diagonalAugmentation_eq_terminal (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    diagonalAugmentation W x = SSet.stdSimplex.isTerminalObj₀.from
      (SSet.simplicialDiagonalFunctor.obj (diagram W x)) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The retained diagonal basepoint map is the original whole constant simplicial map. -/
theorem diagonalBasepointMap_eq_const (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    diagonalBasepointMap W x = SSet.const (diagonalBasepoint W x) := by
  change diagonalBasepointMap W x = SSet.const (SSet.yonedaEquiv (diagonalBasepointMap W x))
  rw [← SSet.yonedaEquiv_symm_zero]
  exact (SSet.yonedaEquiv.symm_apply_apply _).symm

/-- The whole original diagonal augmentation-section roundtrip is literally constant at the same retained point. -/
theorem diagonal_nativeRetraction_eq_const (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.simplicialDiagonalFunctor.map (nativeRetraction W x) =
      SSet.const (diagonalBasepoint W x) := by
  rw [diagonal_nativeRetraction, diagonalAugmentation_eq_terminal, diagonalBasepointMap_eq_const]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- The original interval contraction starts at its literal identity-edge constant point. -/
def nativeDiagonalPointContraction (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.Homotopy (SSet.const (diagonalBasepoint W x))
      (𝟙 (SSet.simplicialDiagonalFunctor.obj (diagram W x))) := by
  have h := nativeDiagonalContraction W x
  rw [diagonal_nativeRetraction_eq_const] at h
  exact h

end SimplicialSpace.LeftDecalageObject
