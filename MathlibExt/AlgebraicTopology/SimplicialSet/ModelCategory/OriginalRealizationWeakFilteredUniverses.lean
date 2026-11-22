/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.OriginalRealizationWeakFilteredColimits

/-!
# The SAME realization weak-colimit map at independent small diagram universes

The actual indexing equivalence resizes its presentation and preserves
both full original cocones and their original natural comparison.
The SAME proved complete weak-colimit class returns weakness of the
original supplied map at its unchanged independent indexing universes.
-/

@[expose] public section



noncomputable section
universe u v w
open CategoryTheory Limits

namespace SSet

private theorem filteredOfUnivLE (P : MorphismProperty SSet.{u})
    [UnivLE.{w, u}] [UnivLE.{v, u}] [P.IsStableUnderFilteredColimits.{u, u}] :
    P.IsStableUnderFilteredColimits.{w, v} := by
  constructor
  intro J _ _
  let e := ((ShrinkHoms.equivalence.{u} J).trans (Shrink.equivalence _)).symm
  have := IsFiltered.of_equivalence e.symm
  rw [MorphismProperty.isStableUnderColimitsOfShape_iff_colimitsOfShape_le]
  rw [← P.colimitsOfShape_eq_of_equivalence e]
  exact MorphismProperty.colimitsOfShape_le (W := P)

/-- The complete original weak class retains genuine filtered colimits at independent small diagram universes. -/
instance realizationWeakFilteredColimitsUnivLE [UnivLE.{w, u}] [UnivLE.{v, u}] :
    MorphismProperty.IsStableUnderFilteredColimits.{w, v} realizationWeakEquivalences.{u} := by
  let _ : MorphismProperty.IsStableUnderFilteredColimits.{u, u} realizationWeakEquivalences.{u} :=
    realizationWeakFilteredColimits
  exact filteredOfUnivLE.{u, v, w} realizationWeakEquivalences

/-- The SAME full original filtered-colimit comparison is weak at independent small object and Hom universes. -/
theorem realizationWeakEquivalences.of_isColimit_filtered_univLE
    {J : Type v} [Category.{w} J] [IsFiltered J] [UnivLE.{v, u}] [UnivLE.{w, u}]
    {F G : J ⥤ SSet.{u}} (α : F ⟶ G)
    {cF : Cocone F} {cG : Cocone G} (hcF : IsColimit cF) (hcG : IsColimit cG)
    (φ : cF.pt ⟶ cG.pt) (hφ : ∀ i, cF.ι.app i ≫ φ = α.app i ≫ cG.ι.app i)
    (hα : ∀ i, realizationWeakEquivalences (α.app i)) : realizationWeakEquivalences φ :=
  MorphismProperty.IsStableUnderColimitsOfShape.condition F G cF cG hcF hcG α hα φ hφ

end SSet
