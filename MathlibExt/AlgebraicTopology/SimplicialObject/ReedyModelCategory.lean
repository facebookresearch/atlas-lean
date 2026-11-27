/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyTrivialClasses
public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeLatchingIso
public import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# The Reedy model category on simplicial objects

A model category structure on `C` induces the Reedy model category on simplicial objects in `C`.
Weak equivalences are pointwise, cofibrations are defined by relative latching maps, and fibrations
are defined by relative matching maps. The instance is opt-in through the
`SimplicialObject.reedyModelCategory` scope.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty
open HomotopicalAlgebra
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The Reedy model category on simplicial objects in a model category. -/
@[instance_reducible]
noncomputable def reedyModelCategory : ModelCategory (SimplicialObject C) := by
  let _ : CategoryWithWeakEquivalences (SimplicialObject C) :=
    { weakEquivalences :=
        (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ }
  let _ : CategoryWithCofibrations (SimplicialObject C) :=
    { cofibrations := reedyLeft (cofibrations C) }
  let _ : CategoryWithFibrations (SimplicialObject C) :=
    { fibrations := reedyRight (fibrations C) }
  let _ : HasFiniteLimits (SimplicialObject C) := inferInstance
  let _ : HasFiniteColimits (SimplicialObject C) := inferInstance
  let _ : (weakEquivalences (SimplicialObject C)).HasTwoOutOfThreeProperty := by
    change ((weakEquivalences C).functorCategory
      SimplexCategoryᵒᵖ).HasTwoOutOfThreeProperty
    infer_instance
  let _ : IsWeakFactorizationSystem
      (trivialCofibrations (SimplicialObject C))
      (fibrations (SimplicialObject C)) := by
    change IsWeakFactorizationSystem
      (reedyLeft (cofibrations C) ⊓
        (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ)
      (reedyRight (fibrations C))
    rw [← reedyLeft_trivialCofibrations_eq]
    infer_instance
  let _ : IsWeakFactorizationSystem
      (cofibrations (SimplicialObject C))
      (trivialFibrations (SimplicialObject C)) := by
    change IsWeakFactorizationSystem
      (reedyLeft (cofibrations C))
      (reedyRight (fibrations C) ⊓
        (weakEquivalences C).functorCategory SimplexCategoryᵒᵖ)
    rw [← reedyRight_trivialFibrations_eq]
    infer_instance
  exact ModelCategory.mk' (SimplicialObject C)

namespace reedyModelCategory

/-- Opt-in Reedy model-category instance on simplicial objects. -/
noncomputable scoped instance instModelCategory :
    ModelCategory (SimplicialObject C) :=
  _root_.CategoryTheory.SimplicialObject.reedyModelCategory

section

open scoped CategoryTheory.SimplicialObject.reedyModelCategory

/-- In the selected Reedy model structure, a simplicial object is cofibrant exactly when all its
absolute latching maps are cofibrations in the base category. -/
theorem isCofibrant_iff_latchingMapsIn (X : SimplicialObject C) :
    IsCofibrant X ↔ X.LatchingMapsIn (cofibrations C) := by
  rw [HomotopicalAlgebra.isCofibrant_iff,
    HomotopicalAlgebra.cofibration_iff]
  change reedyLeft (cofibrations C) (initial.to X) ↔
    ∀ n : ℕ, cofibrations C (latchingMap X n)
  constructor
  · intro h n
    exact ((cofibrations C).arrow_mk_iso_iff
      (relativeLatchingMapInitialArrowIso X n)).mp (h n)
  · intro h n
    exact ((cofibrations C).arrow_mk_iso_iff
      (relativeLatchingMapInitialArrowIso X n)).mpr (h n)

end

end reedyModelCategory

end CategoryTheory.SimplicialObject
