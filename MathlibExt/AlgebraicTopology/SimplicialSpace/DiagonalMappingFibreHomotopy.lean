/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.DiagonalMappingFibreCylinder

/-!
# The original mapping-fibre interval homotopy in the diagonal

Package the actual whole-row interval evaluation with its two proved
original endpoint equations. The homotopy keeps every original mapping
edge and every original interval simplex.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The full original mapping edge gives its actual diagonal source-to-target interval homotopy. -/
def mappingFibreDiagonalHomotopy (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.Homotopy (mappingFibreDiagonalSource W x y) (mappingFibreDiagonalTarget W x y) := by
  change SSet.RelativeMorphism.Homotopy
    (SSet.RelativeMorphism.botEquiv.symm (mappingFibreDiagonalSource W x y))
    (SSet.RelativeMorphism.botEquiv.symm (mappingFibreDiagonalTarget W x y))
  exact {
    h := mappingFibreDiagonalCylinder W x y
    h₀ := mappingFibreDiagonalCylinder_zero W x y
    h₁ := mappingFibreDiagonalCylinder_one W x y
    rel := by
      ext e z
      rcases z with ⟨⟨a, ha⟩, t⟩
      cases ha }

/-- The actual homotopy is the literal original whole-row interval cylinder. -/
theorem mappingFibreDiagonalHomotopy_h (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingFibreDiagonalHomotopy W x y).h = mappingFibreDiagonalCylinder W x y := rfl

end SimplicialSpace.LeftDecalageObject
