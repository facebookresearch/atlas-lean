/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Adjunction.RelativeProjectivity
public import MathlibExt.CategoryTheory.Monad.AdjunctionBarFunctor

/-!
# Relative projectivity of adjunction Bar terms

Each term of the free Bar of an adjunction is projective relative to the right adjoint. The
restricted augmentation is split by the adjunction unit.
-/

@[expose] public section

open CategoryTheory Opposite
universe uC vC uD vD

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F : C ⥤ D} {U : D ⥤ C}

/-- Each simplicial Bar term has the full canonical relative lifting property. -/
theorem freeBar_isRelativeProjective (adj : F ⊣ U) (M : D) (n : ℕ) :
    U.IsRelativeProjective ((adj.freeBar M).obj (Opposite.op (SimplexCategory.mk n))) := by
  rw [freeBar_obj]
  exact adj.isRelativeProjective_obj ((Monad.monadPow adj.toMonad n).obj (U.obj M))

/-- The image of the degree-zero Bar augmentation is split by the unit. -/
def freeBarAugmentationSplitEpi (adj : F ⊣ U) (M : D) :
    SplitEpi (U.map ((adj.freeBarAugmented M).hom.app (Opposite.op (SimplexCategory.mk 0)))) where
  section_ := adj.unit.app (U.obj M)
  id := by
    rw [freeBarAugmented_hom_zero]
    exact (adj.mapCounitSplitEpi M).id

/-- The restricted augmentation section retains the literal adjunction unit. -/
@[simp]
theorem freeBarAugmentationSplitEpi_section (adj : F ⊣ U) (M : D) :
    (adj.freeBarAugmentationSplitEpi M).section_ = adj.unit.app (U.obj M) := rfl

end CategoryTheory.Adjunction
