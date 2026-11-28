/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingZeroUnit
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The original marked coefficient and terminal-point equivalence

The original maximally marked zero simplex is terminal. Its canonical
slice equivalence retains every entire marked carrier and map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory Limits
open scoped Simplicial

namespace SSet.Marked

/-- Insert the unique original point projection and retain each marked object and map. -/
def coefficientPointEquivalence : Marked.{u} ≌ Over (max (Δ[0] : SSet.{u})) :=
  (Over.equivalenceOfIsTerminal (parameterZeroIsTerminal .maximal)).symm

/-- Every coefficient maps to the original marked point slice with the same total carrier. -/
theorem coefficientPointEquivalence_obj (A : Marked.{u}) :
    (coefficientPointEquivalence.functor.obj A).left = A := rfl

/-- The original coefficient map is retained by the canonical point-slice equivalence. -/
theorem coefficientPointEquivalence_map {A D : Marked.{u}} (f : A ⟶ D) :
    (coefficientPointEquivalence.functor.map f).left = f := rfl

end SSet.Marked
