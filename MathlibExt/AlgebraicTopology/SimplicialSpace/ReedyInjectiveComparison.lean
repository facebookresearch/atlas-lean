/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyModel
import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# The Reedy model and the whole injective lifting class

The three classes of the named vertical Reedy model are monomorphisms,
objectwise realization weak equivalences and the whole right lifting class
of objectwise scalar trivial cofibrations. This whole lifting class also
has the native every-degree relative matching characterization.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped Simplicial

namespace SimplicialSpace.ReedyModel

private theorem selected_cofibrations_eq_monomorphisms :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    cofibrations SimplicialSpace.{u} = monomorphisms SimplicialSpace.{u} := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  apply MorphismProperty.ext
  intro X Y f
  exact (HomotopicalAlgebra.cofibration_iff f).symm.trans (cofibration_iff f)

private theorem selected_weakEquivalences_eq_objectwise :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    weakEquivalences SimplicialSpace.{u} =
      (SSet.realizationWeakEquivalences.{u}.functorCategory
        SimplexCategoryᵒᵖ).inverseImage forget := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  rfl

private theorem selected_trivialCofibrations_eq_objectwise :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    trivialCofibrations SimplicialSpace.{u} =
      ((monomorphisms SSet.{u} ⊓ SSet.realizationWeakEquivalences.{u}).functorCategory
        SimplexCategoryᵒᵖ).inverseImage forget := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  change (cofibrations SimplicialSpace.{u} ⊓ weakEquivalences SimplicialSpace.{u}) = _
  rw [selected_cofibrations_eq_monomorphisms, selected_weakEquivalences_eq_objectwise]
  have hmono : monomorphisms SimplicialSpace.{u} =
      ((monomorphisms SSet.{u}).functorCategory SimplexCategoryᵒᵖ).inverseImage forget := by
    rw [MorphismProperty.functorCategory_monomorphisms]
    apply MorphismProperty.ext
    intro X Y f
    exact (mono_forget_map_iff f).symm
  rw [hmono]
  apply MorphismProperty.ext
  intro X Y f
  change
    ((∀ n : SimplexCategoryᵒᵖ, Mono ((forget.map f).app n)) ∧
      ∀ n : SimplexCategoryᵒᵖ,
        SSet.realizationWeakEquivalences ((forget.map f).app n)) ↔
      ∀ n : SimplexCategoryᵒᵖ,
        Mono ((forget.map f).app n) ∧
          SSet.realizationWeakEquivalences ((forget.map f).app n)
  constructor
  · rintro ⟨hc, hw⟩ n
    exact ⟨hc n, hw n⟩
  · intro h
    exact ⟨fun n => (h n).1, fun n => (h n).2⟩

private theorem selected_fibrations_eq_objectwiseTrivialCofibrations_rlp :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    fibrations SimplicialSpace.{u} =
      (((monomorphisms SSet.{u} ⊓ SSet.realizationWeakEquivalences.{u}).functorCategory
        SimplexCategoryᵒᵖ).inverseImage forget).rlp := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  exact (trivialCofibrations_rlp SimplicialSpace.{u}).symm.trans
    (congrArg (fun P : MorphismProperty SimplicialSpace.{u} => P.rlp)
      selected_trivialCofibrations_eq_objectwise)

/-- All three getters of the existing named model agree with the original
monomorphisms, objectwise realization weak equivalences and the whole original
right lifting class of objectwise scalar trivial cofibrations. -/
theorem selectedReedy_injective_classes :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    (cofibrations SimplicialSpace.{u} = monomorphisms SimplicialSpace.{u}) ∧
    (weakEquivalences SimplicialSpace.{u} =
      (SSet.realizationWeakEquivalences.{u}.functorCategory
        SimplexCategoryᵒᵖ).inverseImage forget) ∧
    (fibrations SimplicialSpace.{u} =
      (((monomorphisms SSet.{u} ⊓ SSet.realizationWeakEquivalences.{u}).functorCategory
        SimplexCategoryᵒᵖ).inverseImage forget).rlp) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  exact ⟨selected_cofibrations_eq_monomorphisms,
    selected_weakEquivalences_eq_objectwise,
    selected_fibrations_eq_objectwiseTrivialCofibrations_rlp⟩

/-- The whole original-arrow injective RLP is equivalent to all actual native
relative matching conditions, with degree zero included. -/
theorem objectwiseTrivialCofibrations_rlp_iff_matching
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    (((monomorphisms SSet.{u} ⊓ SSet.realizationWeakEquivalences.{u}).functorCategory
      SimplexCategoryᵒᵖ).inverseImage forget).rlp f ↔
      ∀ n : ℕ, SSet.modelCategoryQuillen.J.rlp
        (SimplicialObject.relativeMatchingMap (forget.map f) n) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  rw [← selected_fibrations_eq_objectwiseTrivialCofibrations_rlp]
  exact (HomotopicalAlgebra.fibration_iff f).symm.trans (fibration_iff f)

end SimplicialSpace.ReedyModel
