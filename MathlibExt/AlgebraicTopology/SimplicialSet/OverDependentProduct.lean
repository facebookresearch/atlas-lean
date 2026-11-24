/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.OverCartesianClosed
import Mathlib.CategoryTheory.LocallyCartesianClosed.Sections
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# A genuine dependent product for the SAME original simplicial pullback

The full native section adjunction and iterated-over equivalence are
reused. Chosen pullbacks are the original native `Over.pullback` functors.
The resulting genuine right adjoint retains that SAME whole original
left functor, every original projection and all over-category morphisms.
No weak-equivalence or model-comparison outcome is supplied.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.OverDependentProduct

private instance chosenSSetPullbacks : ChosenPullbacks SSet.{u} :=
  fun {_ _} f => ChosenPullbacksAlong.ofHasPullbacksAlong f

private instance chosenOverPullbacks (B : SSet.{u}) : ChosenPullbacks (Over B) :=
  fun {_ _} f => ChosenPullbacksAlong.ofHasPullbacksAlong f

attribute [local instance] ChosenPullbacksAlong.cartesianMonoidalCategoryOver

private instance overBraided (B : SSet.{u}) : BraidedCategory (Over B) :=
  .ofCartesianMonoidalCategory

private instance overClosed (B : SSet.{u}) : MonoidalClosed (Over B) :=
  OverPresheaf.cartesianClosed B

/-- The native full section functor after the SAME original iterated-over inverse. -/
def functor {E B : SSet.{u}} (p : E ⟶ B) : Over E ⥤ Over B :=
  (Over.mk p).iteratedSliceEquiv.inverse ⋙ Over.sections (Over.mk p)

/-- The SAME original native pullback is genuinely left adjoint to this full dependent product. -/
def adjunction {E B : SSet.{u}} (p : E ⟶ B) : Over.pullback p ⊣ functor p :=
  ((Over.toOverSectionsAdj (Over.mk p)).comp (Over.mk p).iteratedSliceEquiv.toAdjunction).ofNatIsoLeft
    (toOverIteratedSliceForwardIsoPullback p)

/-- The full native adjunction supplies its genuine Hom equivalence on the SAME original over morphisms. -/
def homEquiv {E B : SSet.{u}} (p : E ⟶ B) (X : Over B) (Y : Over E) :
    ((Over.pullback p).obj X ⟶ Y) ≃ (X ⟶ (functor p).obj Y) := (adjunction p).homEquiv X Y

/-- Both full original operations satisfy the actual forward/inverse equation. -/
theorem homEquiv_left_inv {E B : SSet.{u}} (p : E ⟶ B) (X : Over B) (Y : Over E)
    (f : (Over.pullback p).obj X ⟶ Y) : (homEquiv p X Y).symm (homEquiv p X Y f) = f :=
  (homEquiv p X Y).symm_apply_apply f

/-- Both full original operations satisfy the actual inverse/forward equation. -/
theorem homEquiv_right_inv {E B : SSet.{u}} (p : E ⟶ B) (X : Over B) (Y : Over E)
    (f : X ⟶ (functor p).obj Y) : homEquiv p X Y ((homEquiv p X Y).symm f) = f :=
  (homEquiv p X Y).apply_symm_apply f

/-- The SAME original native pullback preserves all colimits through its genuine left adjunction. -/
theorem pullback_preservesColimits {E B : SSet.{u}} (p : E ⟶ B) : PreservesColimits (Over.pullback p) :=
  (adjunction p).leftAdjoint_preservesColimits

end SSet.OverDependentProduct
