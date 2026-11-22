/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.QuillenFibrantCriterion
import MathlibExt.AlgebraicTopology.SimplicialSpace.HorizontalDivision
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkModelCategory
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkRowFibrations

/-!
# Every rowwise categorical weak arrow is genuine Rezk weak

The actual horizontal and Rezk models have their original monomorphism
cofibrations. Canonical genuine row fibrations and the native JT7.15/Brown
criterion give weak containment for every original arrow.

Source: Joyal–Tierney Theorem 4.5, printed page 23.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace SimplicialSpace

/-- Every original rowwise categorical weak arrow is weak in the actual Rezk model. -/
theorem rowwiseCategoricalEquivalences_le_rezkWeakEquivalences :
    rowwiseCategoricalEquivalences.{u} ≤ rezkWeakEquivalences.{u} := by
  intro X Y f hf
  have h : RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences f :=
    @Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_allObjectsCofibrant_of_fibrantCriterion
      SimplicialSpace.{u} inferInstance HorizontalModel.modelCategory
      SimplicialSpace.{u} inferInstance RezkModel.modelCategory
      (𝟭 _) (𝟭 _) (Adjunction.id)
      (by
        intro A B i hi
        have hiMono : Mono i := by
          let _ : ModelCategory SimplicialSpace.{u} := HorizontalModel.modelCategory
          exact (HorizontalModel.cofibration_iff i).mp
            ((HomotopicalAlgebra.cofibration_iff (f := i)).mpr hi)
        change RezkModel.modelCategory.categoryWithCofibrations.cofibrations i
        rw [RezkModel.modelCategory_cofibrations]
        exact hiMono)
      (by
        intro A B p hp
        have hA : completeSegalSpaces A :=
          (RezkModel.isFibrant_iff_completeSegalSpaces A).mp hp.2.1
        have hB : completeSegalSpaces B :=
          (RezkModel.isFibrant_iff_completeSegalSpaces B).mp hp.2.2
        have hpR := hp.1
        change RezkModel.modelCategory.categoryWithFibrations.fibrations p at hpR
        let _ : ModelCategory SimplicialSpace.{u} := HorizontalModel.modelCategory
        exact (HomotopicalAlgebra.fibration_iff (f := p)).mp
          ((HorizontalModel.fibration_iff_hasCategoricalRowPullbackHoms p).mpr
            (hasCategoricalRowPullbackHom_of_rezkFibration p hA hB hpR)))
      HorizontalModel.isCofibrant X Y f
      (by
        let _ : ModelCategory SimplicialSpace.{u} := HorizontalModel.modelCategory
        exact (HomotopicalAlgebra.weakEquivalence_iff f).mp
          ((HorizontalModel.weakEquivalence_iff f).mpr hf))
  simpa only [RezkModel.modelCategory_weakEquivalences] using h

end SimplicialSpace
