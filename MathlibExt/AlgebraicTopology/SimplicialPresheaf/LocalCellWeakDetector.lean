/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalCellReplacement
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalWhitehead
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# The same original local replacement detects all original weak arrows

Both original locally weak unit components and their literal naturality square
identify the original weak test on f with that on the same replacement image.
The actual local-fibrant replacement endpoints permit original LocalWhitehead.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w i

open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

/-- The same arbitrary original arrow is locally weak exactly when its actual
original cell-replacement image belongs to the actual base weak class. -/
theorem originalLocalEquivalence_iff_weak_originalLocalCellReplacement
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B) :
    originalLocalEquivalences S f ↔
      weakEquivalences (SimplicialPresheaf.{u} D)
        ((originalLocalCellReplacement S).map f) := by
  let : (originalLocalEquivalences S).HasTwoOutOfThreeProperty :=
    originalLocalEquivalences_hasTwoOutOfThreeProperty S
  calc
    originalLocalEquivalences S f ↔
        originalLocalEquivalences S (f ≫ (originalLocalCellUnit S).app B) :=
      ((originalLocalEquivalences S).postcomp_iff f ((originalLocalCellUnit S).app B)
        (originalLocalCellUnit_mono_weak S B).2).symm
    _ ↔ originalLocalEquivalences S
        ((originalLocalCellUnit S).app A ≫ (originalLocalCellReplacement S).map f) := by
      rw [originalLocalCellUnit_naturality S f]
    _ ↔ originalLocalEquivalences S ((originalLocalCellReplacement S).map f) :=
      (originalLocalEquivalences S).precomp_iff ((originalLocalCellUnit S).app A)
        ((originalLocalCellReplacement S).map f) (originalLocalCellUnit_mono_weak S A).2
    _ ↔ weakEquivalences (SimplicialPresheaf.{u} D)
        ((originalLocalCellReplacement S).map f) :=
      originalLocalEquivalence_iff_weakEquivalence_of_localFibrant S
        ((originalLocalCellReplacement S).map f)
        (originalLocalCellReplacement_localFibrant S A)
        (originalLocalCellReplacement_localFibrant S B)

/-- The original local weak class is the literal inverse image of the actual
base weak class under the same original replacement functor. -/
theorem originalLocalEquivalences_eq_inverseImage_originalLocalCellReplacement
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    originalLocalEquivalences S =
      (weakEquivalences (SimplicialPresheaf.{u} D)).inverseImage
        (originalLocalCellReplacement S) := by
  ext A B f
  exact originalLocalEquivalence_iff_weak_originalLocalCellReplacement S f

end SimplicialPresheaf.InjectiveKan
