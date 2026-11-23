/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWeakFiniteSubarrow
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWColimits
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
# Filtered colimits of the full scalar realization weak class

The same scalar horn completion sends both original colimit cocones to
colimit cocones of Kan complexes. Full Kan weak closure and reflection by
that completion detect the original displayed colimit map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace SSet

/-- Full realization weak equivalences are stable under working-small filtered
colimits, without Kan or monicity assumptions on the original endpoints. -/
theorem realizationWeakEquivalences_stableUnderFilteredColimits :
    MorphismProperty.IsStableUnderFilteredColimits.{u, u}
      (realizationWeakEquivalences : MorphismProperty SSet.{u}) where
  isStableUnderColimitsOfShape J _ _ := by
    constructor
    intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
    let C : SSet.{u} ⥤ SSet.{u} := KanWeakInterpolation.completion
    let _ (X : SSet.{u}) : KanComplex (C.obj X) :=
      KanWeakInterpolation.completion_isKan X
    let _ : PreservesColimitsOfShape J C :=
      KanWeakInterpolation.completion_preservesFilteredColimitsOfShape J
    have hC : KanComplex.W (C.map φ) :=
      MorphismProperty.IsStableUnderColimitsOfShape.condition
        (X₁ ⋙ C) (X₂ ⋙ C) (C.mapCocone c₁) (C.mapCocone c₂)
        (isColimitOfPreserves C hc₁) (isColimitOfPreserves C hc₂)
        (Functor.whiskerRight f C)
        (fun j ↦ (KanComplex.W_iff_realizationWeakEquivalence (C.map (f.app j))).mpr
          ((KanWeakInterpolation.completion_map_weak_iff (f.app j)).mpr (hf j)))
        (C.map φ) (fun j ↦ by
          simpa only [Functor.mapCocone_ι_app, Functor.whiskerRight_app,
            ← Functor.map_comp] using congrArg C.map (hφ j))
    exact (KanWeakInterpolation.completion_map_weak_iff φ).mp
      ((KanComplex.W_iff_realizationWeakEquivalence (C.map φ)).mp hC)

end SSet
