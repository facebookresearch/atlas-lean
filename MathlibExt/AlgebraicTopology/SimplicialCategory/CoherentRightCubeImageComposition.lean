/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeCosimplicialMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontOperators

/-!
# Actual direct-image composition in original right-cube operators

Original right-join direct images preserve simplex-operator composition
before structural zero adjunction. The two target front labels are the
same original composite label. This supplies the exact quotient
comparison after the proved front-prefix relation removes the extra
intermediate zero prefix.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.CoherentRealization.RightCubeImageComposition
open PathLastMaximum PathMaximumOperators
variable {n m k : ℕ}

/-- The whole original right-join direct-image function is the composite of the two original lifted
  functions, in the same supplied universe. -/
theorem extension_lift_comp (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (ψ : SimplexCategory.mk m ⟶ SimplexCategory.mk k) :
    (fun x : ULift.{u} (Fin (n + 2)) => ULift.up.{u} ((extension (θ ≫ ψ)).toOrderHom x.down)) =
      (fun x : ULift.{u} (Fin (n + 2)) => ULift.up.{u} ((extension ψ).toOrderHom ((extension θ).toOrderHom
        x.down))) := by
  funext x
  exact congrArg ULift.up (congrArg (fun θ => θ.toOrderHom x.down) (FixedFrontOperators.extension_comp θ ψ))

/-- The original successive direct-image path subsets are precisely the composite original right-join direct image. -/
theorem image_comp_I (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (ψ : SimplexCategory.mk m ⟶ SimplexCategory.mk k) (i : Fin (n + 1)) (p : LastPath.{u} i) :
    (image ψ (θ.toOrderHom i) (image θ i p)).I = (image (θ ≫ ψ) i p).I := by
  change (extension ψ).toOrderHom.uliftMap '' ((extension θ).toOrderHom.uliftMap '' p.I) =
    (extension (θ ≫ ψ)).toOrderHom.uliftMap '' p.I
  rw [Set.image_image]
  exact congrArg (fun f : ULift.{u} (Fin (n + 2)) → ULift.{u} (Fin (k + 2)) => f '' p.I)
    (extension_lift_comp.{u} θ ψ).symm

end CategoryTheory.CoherentRealization.RightCubeImageComposition
