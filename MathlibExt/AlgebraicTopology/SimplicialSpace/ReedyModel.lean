/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.Basic
import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyModelCategory
import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
import Mathlib.AlgebraicTopology.ModelCategory.Transport

/-!
# The named Reedy model on the designated simplicial-space carrier

The actual Kan–Quillen model on simplicial sets gives the actual raw Reedy
model. Native equivalence transport puts that model on `SimplicialSpace`, keeping
its three classes explicit. No global default model is installed.
-/

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped Simplicial

namespace SimplicialSpace.ReedyModel

private abbrev rawModel : ModelCategory (SimplicialObject SSet.{u}) := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  exact CategoryTheory.SimplicialObject.reedyModelCategory

/-- The unconditional named Reedy model, transported to the designated carrier. -/
@[instance_reducible]
def modelCategory : ModelCategory SimplicialSpace.{u} := by
  let R := rawModel.{u}
  let _ : ModelCategory (SimplicialObject SSet.{u}) := R
  let _ : CategoryWithCofibrations SimplicialSpace.{u} :=
    { cofibrations := R.categoryWithCofibrations.cofibrations.inverseImage SimplicialSpace.forget }
  let _ : CategoryWithFibrations SimplicialSpace.{u} :=
    { fibrations := R.categoryWithFibrations.fibrations.inverseImage SimplicialSpace.forget }
  let _ : CategoryWithWeakEquivalences SimplicialSpace.{u} :=
    { weakEquivalences :=
        R.categoryWithWeakEquivalences.weakEquivalences.inverseImage SimplicialSpace.forget }
  exact ModelCategory.transport SimplicialSpace.equivalenceSimplicialObject rfl rfl rfl

/-- Weak equivalences are the levelwise realization weak equivalences. -/
theorem weakEquivalence_iff {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    WeakEquivalence f ↔ ∀ n : ℕ,
      SSet.realizationWeakEquivalences ((SimplicialSpace.forget.map f).app (Opposite.op ⦋n⦌)) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  rw [HomotopicalAlgebra.weakEquivalence_iff]
  change (∀ a : SimplexCategoryᵒᵖ,
    SSet.realizationWeakEquivalences ((SimplicialSpace.forget.map f).app a)) ↔ _
  constructor
  · intro h n
    exact h (Opposite.op ⦋n⦌)
  · intro h a
    exact h a.unop.len

/-- Fibrations satisfy every actual relative matching condition, including zero. -/
theorem fibration_iff {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    Fibration f ↔ ∀ n : ℕ,
      SSet.modelCategoryQuillen.J.rlp
        (SimplicialObject.relativeMatchingMap (SimplicialSpace.forget.map f) n) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  rw [HomotopicalAlgebra.fibration_iff]
  rfl

/-- Cofibrations in this same named model are exactly the original monomorphisms. -/
theorem cofibration_iff {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    Cofibration f ↔ Mono f := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  rw [HomotopicalAlgebra.cofibration_iff]
  change SimplicialObject.reedyLeft (monomorphisms SSet.{u}) (SimplicialSpace.forget.map f) ↔ Mono f
  rw [SimplicialObject.reedyLeft_monomorphisms_eq]
  exact SimplicialSpace.mono_forget_map_iff f

end SimplicialSpace.ReedyModel
