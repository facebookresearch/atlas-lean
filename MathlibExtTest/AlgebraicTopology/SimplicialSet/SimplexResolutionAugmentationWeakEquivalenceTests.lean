/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolutionAugmentationWeakEquivalence

/-!
# Simplex-resolution augmentation weak-equivalence tests

These tests pin both low fixed degrees, the strict transported row
augmentation, an inner-row application, and the final diagonal augmentation.
-/

noncomputable section

open CategoryTheory Opposite Simplicial

open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace SimplexResolutionAugmentationWeakEquivalenceTests

universe u

variable {Z Y : SSet.{u}} (p : Z ⟶ Y)

example :
    SSet.realizationWeakEquivalences
      (SSet.simplexResolutionDegreeAugmentation p
        (Opposite.op (SimplexCategory.mk 0))) :=
  SSet.simplexResolutionDegreeAugmentation_mem_realizationWeakEquivalences
    p (Opposite.op (SimplexCategory.mk 0))

example :
    SSet.realizationWeakEquivalences
      (SSet.simplexResolutionDegreeAugmentation p
        (Opposite.op (SimplexCategory.mk 1))) :=
  SSet.simplexResolutionDegreeAugmentation_mem_realizationWeakEquivalences
    p (Opposite.op (SimplexCategory.mk 1))

example (a : SimplexCategoryᵒᵖ) :
    SSet.terminalWeightDegreeAugmentation
        (SSet.simplexPullbackCocone p) a =
      SSet.simplexResolutionDegreeAugmentation p a :=
  SSet.terminalWeightDegreeAugmentation_simplexPullbackCocone p a

example :
    SSet.realizationWeakEquivalences
      ((SSet.simplicialTransposeFunctor.map
        (SSet.wbarAugmentation (SSet.simplexPullbackCocone p))).app
          (Opposite.op (SimplexCategory.mk 1))) :=
  SSet.simplexResolutionWbarAugmentation_inner_row_mem p
    (Opposite.op (SimplexCategory.mk 1))

example :
    SSet.realizationWeakEquivalences
      ((SSet.simplicialTransposeFunctor.map
        (SSet.wbarAugmentation (SSet.simplexPullbackCocone p))).app
          (Opposite.op (SimplexCategory.mk 0))) :=
  SSet.simplexResolutionWbarAugmentation_inner_row_mem p
    (Opposite.op (SimplexCategory.mk 0))

example :
    SSet.realizationWeakEquivalences
      (SSet.simplexResolutionAugmentation p) :=
  SSet.simplexResolutionAugmentation_mem_realizationWeakEquivalences p

section UniverseOne

variable {Z₁ Y₁ : SSet.{1}} (p₁ : Z₁ ⟶ Y₁)

example : SSet.realizationWeakEquivalences
    (SSet.simplexResolutionAugmentation p₁) :=
  SSet.simplexResolutionAugmentation_mem_realizationWeakEquivalences p₁

end UniverseOne

section UniverseZero

variable {Z₀ Y₀ : SSet.{0}} (p₀ : Z₀ ⟶ Y₀)

example : SSet.realizationWeakEquivalences
    (SSet.simplexResolutionAugmentation p₀) :=
  SSet.simplexResolutionAugmentation_mem_realizationWeakEquivalences p₀

end UniverseZero

section BoundaryFixtures

example : SSet.realizationWeakEquivalences
    (SSet.simplexResolutionAugmentation (𝟙 (⊥_ SSet.{0}))) :=
  SSet.simplexResolutionAugmentation_mem_realizationWeakEquivalences _

private abbrev disconnected : SSet.{0} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (Fin 2)

example : SSet.realizationWeakEquivalences
    (SSet.simplexResolutionAugmentation (𝟙 disconnected)) :=
  SSet.simplexResolutionAugmentation_mem_realizationWeakEquivalences _

example : SSet.realizationWeakEquivalences
    (SSet.simplexResolutionAugmentation (𝟙 (Δ[0] : SSet.{0}))) :=
  SSet.simplexResolutionAugmentation_mem_realizationWeakEquivalences _

example : SSet.realizationWeakEquivalences
    (SSet.simplexResolutionAugmentation (𝟙 (Δ[1] : SSet.{0}))) :=
  SSet.simplexResolutionAugmentation_mem_realizationWeakEquivalences _

end BoundaryFixtures

#print axioms SSet.simplexResolutionDegreeAugmentation_mem_realizationWeakEquivalences
#print axioms SSet.terminalWeightDegreeAugmentation_simplexPullbackCocone
#print axioms SSet.simplexResolutionWbarAugmentation_inner_row_mem
#print axioms SSet.simplexResolutionAugmentation_mem_realizationWeakEquivalences

end SimplexResolutionAugmentationWeakEquivalenceTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
