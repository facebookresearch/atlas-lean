/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.TotalComparisonQuillen
import MathlibExt.AlgebraicTopology.SimplicialSpace.TotalComparisonFirstComposite
import MathlibExt.AlgebraicTopology.SimplicialSpace.JoyalTierneyQuillenEquivalence
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceCancellation

/-!
# The full second Joyal–Tierney Quillen equivalence

The original composite adjunction's whole Hom equation and its two actual
weak isomorphism factors give the full composite Hovey criterion. Native left
cancellation then gives the total Quillen equivalence and its criterion on
every original cofibrant source, fibrant target and original arrow.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace SimplicialSpace.TotalSpace

private theorem firstTotalComposite_isQuillenEquivalence :
    letI : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    firstTotalCompositeAdjunction.{u}.IsQuillenEquivalence := by
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  let _ : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  let _ : comparisonAdjunction.{u}.IsQuillenEquivalence :=
    comparisonAdjunction_isQuillenEquivalence
  let _ : adjunction.{u}.IsQuillenAdjunction := adjunction_isQuillen
  have hQA : firstTotalCompositeAdjunction.{u}.IsQuillenAdjunction := by
    change (comparisonAdjunction.comp adjunction).IsQuillenAdjunction
    infer_instance
  refine { toIsQuillenAdjunction := hQA, homEquiv_weakEquivalence_iff := ?_ }
  intro A Q _ _ f
  have he : weakEquivalences JoyalSSet.{u} (firstTotalLeftIso.inv.app A) :=
    mem_weakEquivalences _
  have hr : weakEquivalences JoyalSSet.{u} (totalFirstRightIso.hom.app Q) :=
    mem_weakEquivalences _
  calc
    weakEquivalences JoyalSSet.{u} f ↔
        weakEquivalences JoyalSSet.{u} (firstTotalLeftIso.inv.app A ≫ f) :=
      ((weakEquivalences JoyalSSet.{u}).precomp_iff
        (firstTotalLeftIso.inv.app A) f he).symm
    _ ↔ weakEquivalences JoyalSSet.{u}
        (firstTotalCompositeAdjunction.homEquiv A Q f ≫ totalFirstRightIso.hom.app Q) := by
      rw [firstTotalComposite_homEquiv]
    _ ↔ weakEquivalences JoyalSSet.{u} (firstTotalCompositeAdjunction.homEquiv A Q f) :=
      (weakEquivalences JoyalSSet.{u}).postcomp_iff
        (firstTotalCompositeAdjunction.homEquiv A Q f) (totalFirstRightIso.hom.app Q) hr

/-- The actual total adjunction is a Quillen equivalence for the original named
Rezk and Joyal models; all class inputs are established internally. -/
theorem adjunction_isQuillenEquivalence :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    letI : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    adjunction.{u}.IsQuillenEquivalence := by
  let _ : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  let _ : comparisonAdjunction.{u}.IsQuillenEquivalence :=
    comparisonAdjunction_isQuillenEquivalence
  let _ : adjunction.{u}.IsQuillenAdjunction := adjunction_isQuillen
  let _ : (comparisonAdjunction.{u}.comp adjunction.{u}).IsQuillenEquivalence :=
    firstTotalComposite_isQuillenEquivalence
  exact Adjunction.IsQuillenEquivalence.cancel_left comparisonAdjunction adjunction

/-- The full Hovey iff uses the same original source, target and arrow. The
source need only be cofibrant, and no replacement or QE outcome is supplied. -/
theorem adjunction_homEquiv_weakEquivalence_iff :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    letI : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
    ∀ (X : SimplicialSpace.{u}) (Q : JoyalSSet.{u}),
      IsCofibrant X → IsFibrant Q → ∀ (f : left.obj X ⟶ Q),
        WeakEquivalence f ↔ WeakEquivalence (adjunction.homEquiv X Q f) := by
  let _ : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  let _ : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  intro X Q hX hQ f
  let _ : IsCofibrant X := hX
  let _ : IsFibrant Q := hQ
  let _ : adjunction.{u}.IsQuillenEquivalence := adjunction_isQuillenEquivalence
  exact Adjunction.IsQuillenEquivalence.weakEquivalence_homEquiv_iff
    (adj := adjunction) f

end SimplicialSpace.TotalSpace
