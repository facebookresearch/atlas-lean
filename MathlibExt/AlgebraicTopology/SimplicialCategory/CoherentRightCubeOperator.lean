/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeMaximum
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentPathEndpointTransport

/-!
# Actual original front-operator maps on the right-cube quotient

The original right-join operator maps each last path to its actual
original direct image, then adjoins the structural zero source. This
whole path functor is the operator used by the fixed-front right-cube
resolution. Its original front-prefix relation compatibility is proved
before any quotient operator is asserted.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeOperator
open PathLastMaximum RightCubeRelations PathMaximumOperators
variable {n m : ℕ}

/-- The actual original right-join path-image functor, with the structural zero endpoint adjoined in the target. -/
def functor (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    LastPath.{u} (0 : Fin (n + 1)) ⥤ LastPath.{u} (0 : Fin (m + 1)) :=
  imageFunctor θ 0 ⋙ prependFunctor (θ.toOrderHom 0)

/-- Its whole original path subset is exactly the direct image and the same structural zero target source. -/
theorem functor_path (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (p : LastPath.{u} (0 : Fin (n + 1))) :
    ((functor θ).obj p).I = {ULift.up.{u} (0 : Fin (m + 2))} ∪ (extension θ).toOrderHom.uliftMap '' p.I := rfl

/-- The actual operator image of a whole original last path retains its same original front maximum. -/
theorem maximum_operator (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (p : LastPath.{u} (0 : Fin (n + 1))) :
    maximum 0 ((functor θ).obj p) = θ.toOrderHom (maximum 0 p) := by
  have h := CoherentRealization.RightCubeMaximum.maximum_prepend (θ.toOrderHom 0) (image θ 0 p)
  exact h.trans (maximum_image θ 0 p)

end CategoryTheory.CoherentRealization.RightCubeOperator
