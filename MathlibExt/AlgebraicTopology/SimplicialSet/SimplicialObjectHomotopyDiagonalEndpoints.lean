/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialObjectHomotopyDiagonal

/-!
# The original endpoints of diagonal combinatorial homotopies

The diagonal interval cylinder retains the exact original endpoint maps.
It therefore gives an actual simplicial homotopy between their literal
diagonals, with the same original cylinder map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.Homotopy

variable {X Y : SimplicialObject SSet.{u}} {f g : X ⟶ Y}

/-- The original zero endpoint of the diagonal cylinder is the literal diagonal of the first map. -/
theorem diagonalHomotopyMap_zero (H : SimplicialObject.Homotopy f g) :
    SSet.ι₀ ≫ diagonalHomotopyMap H = SSet.simplicialDiagonalFunctor.map f := by
  apply NatTrans.ext
  funext e
  apply ConcreteCategory.hom_ext
  intro x
  have h := types_congr_hom
    (congrArg (fun p => p.app e) (innerEvaluation H e).toSSetHomotopy.h₀) x
  exact h

/-- The original one endpoint of the diagonal cylinder is the literal diagonal of the second map. -/
theorem diagonalHomotopyMap_one (H : SimplicialObject.Homotopy f g) :
    SSet.ι₁ ≫ diagonalHomotopyMap H = SSet.simplicialDiagonalFunctor.map g := by
  apply NatTrans.ext
  funext e
  apply ConcreteCategory.hom_ext
  intro x
  have h := types_congr_hom
    (congrArg (fun p => p.app e) (innerEvaluation H e).toSSetHomotopy.h₁) x
  exact h

/-- The original SSet-valued combinatorial homotopy induces its actual diagonal simplicial homotopy. -/
def toDiagonalHomotopy (H : SimplicialObject.Homotopy f g) :
    SSet.Homotopy (SSet.simplicialDiagonalFunctor.map f) (SSet.simplicialDiagonalFunctor.map g) := by
  change SSet.RelativeMorphism.Homotopy
    (SSet.RelativeMorphism.botEquiv.symm (SSet.simplicialDiagonalFunctor.map f))
    (SSet.RelativeMorphism.botEquiv.symm (SSet.simplicialDiagonalFunctor.map g))
  exact {
    h := diagonalHomotopyMap H
    h₀ := diagonalHomotopyMap_zero H
    h₁ := diagonalHomotopyMap_one H
    rel := by
      ext e z
      rcases z with ⟨⟨a, ha⟩, t⟩
      cases ha }

/-- The actual diagonal homotopy carries the same original complete interval map. -/
theorem toDiagonalHomotopy_h (H : SimplicialObject.Homotopy f g) :
    H.toDiagonalHomotopy.h = diagonalHomotopyMap H := rfl

end CategoryTheory.SimplicialObject.Homotopy
