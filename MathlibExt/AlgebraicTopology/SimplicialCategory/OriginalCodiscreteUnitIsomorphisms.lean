/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectCodiscreteTerminal
import MathlibExt.AlgebraicTopology.SimplicialCategory.SimplicialUnitScalarFunctorNaturality

/-!
# Unit-category isomorphisms of the same codiscrete terminal

Every Hom of the fixed-label unit target is the same
scalar unit. Its identity unit coefficients give both complete
underlying inverse maps between any object pair. Both inverse
identities are unit-shaped map identities. Every scalar
readback remains the same unit simplex.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.CodiscreteTerminal
variable (O : Type u)

/-- The same unit coefficients give a unit-category isomorphism between any
object pair. -/
def unitIso (a b : (object O).val) :
    ForgetEnrichment.of SSet.{u} a ≅ ForgetEnrichment.of SSet.{u} b where
  hom := ForgetEnrichment.homOf SSet.{u} (𝟙 (𝟙_ SSet.{u}))
  inv := ForgetEnrichment.homOf SSet.{u} (𝟙 (𝟙_ SSet.{u}))
  hom_inv_id := by
    change (_ : 𝟙_ SSet.{u} ⟶ 𝟙_ SSet.{u}) = _
    exact (isTerminalTensorUnit : IsTerminal (𝟙_ SSet.{u})).hom_ext _ _
  inv_hom_id := by
    change (_ : 𝟙_ SSet.{u} ⟶ 𝟙_ SSet.{u}) = _
    exact (isTerminalTensorUnit : IsTerminal (𝟙_ SSet.{u})).hom_ext _ _

/-- The forward unit coefficient retains its same unit simplex at every
scalar degree. -/
theorem unitIso_hom_scalar (a b : (object O).val) (q : SimplexCategoryᵒᵖ) :
    (SSet.unitScalarFunctor (object O).val q).map (unitIso O a b).hom = PUnit.unit := rfl

/-- The inverse unit coefficient retains its same unit simplex at every
scalar degree. -/
theorem unitIso_inv_scalar (a b : (object O).val) (q : SimplexCategoryᵒᵖ) :
    (SSet.unitScalarFunctor (object O).val q).map (unitIso O a b).inv = PUnit.unit := rfl

end CategoryTheory.SimplicialEnrichment.FixedObjects.CodiscreteTerminal
