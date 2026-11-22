/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectBasepoint

/-!
# The literal identity section is the original extra-degeneracy section

The point and row carriers are displayed explicitly in the public identity
section. Its whole map remains the same original fixed-object extra
degeneracy, including the original pullback isomorphism and degeneracy edge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The actual explicitly displayed identity section retains the exact original extra-degeneracy section. -/
theorem sectionZero_eq_extraDegeneracy_section (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) : sectionZero W x = (extraDegeneracy W x).s' := by
  rfl

end SimplicialSpace.LeftDecalageObject
