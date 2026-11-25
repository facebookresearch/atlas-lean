/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialObject.CoefficientPreservation
public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyClasses

/-! # Reedy morphism properties under coefficient functors

The existing whole-arrow comparisons transport an arbitrary isomorphism-invariant
morphism property through postcomposition. No model or comparison result is a premise.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject
namespace CoefficientReedyTransport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D) (P : MorphismProperty D) [P.RespectsIso]

section Latching
variable [HasPushouts C] [HasPushouts D]
  [PreservesColimitsOfShape WalkingSpan F]

/-- Membership of the actual mapped latching arrow equals membership after postcomposition. -/
theorem relativeLatching_mem_iff (k : ℕ)
    [HasColimitsOfShape (latchingIndex k) C]
    [HasColimitsOfShape (latchingIndex k) D]
    [PreservesColimitsOfShape (latchingIndex k) F]
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    P (F.map (relativeLatchingMap f k)) ↔
      P (relativeLatchingMap (whiskerRight f F) k) := by
  exact P.arrow_mk_iso_iff
    ((coefficientRelativeLatchingArrowIso F k).app (Arrow.mk f))

/-- Reedy left-class formation commutes with inverse image under the same coefficient functor. -/
theorem reedyLeft_inverseImage
    [∀ k : ℕ, HasColimitsOfShape (latchingIndex k) C]
    [∀ k : ℕ, HasColimitsOfShape (latchingIndex k) D]
    [∀ k : ℕ, PreservesColimitsOfShape (latchingIndex k) F] :
    reedyLeft (P.inverseImage F) =
      (reedyLeft P).inverseImage ((whiskeringRight SimplexCategoryᵒᵖ C D).obj F) := by
  apply MorphismProperty.ext
  intro X Y f
  change (∀ k : ℕ, P (F.map (relativeLatchingMap f k))) ↔
    ∀ k : ℕ, P (relativeLatchingMap (whiskerRight f F) k)
  exact forall_congr' (fun k => relativeLatching_mem_iff F P k f)
end Latching

section Matching
variable [HasPullbacks C] [HasPullbacks D]
  [PreservesLimitsOfShape WalkingCospan F]

/-- Membership of the actual mapped matching arrow equals membership after postcomposition. -/
theorem relativeMatching_mem_iff (k : ℕ)
    [HasLimitsOfShape (matchingIndex k) C]
    [HasLimitsOfShape (matchingIndex k) D]
    [PreservesLimitsOfShape (matchingIndex k) F]
    {X Y : SimplicialObject C} (f : X ⟶ Y) :
    P (F.map (relativeMatchingMap f k)) ↔
      P (relativeMatchingMap (whiskerRight f F) k) := by
  exact P.arrow_mk_iso_iff
    ((coefficientRelativeMatchingArrowIso F k).app (Arrow.mk f))

/-- Reedy right-class formation commutes with inverse image under the same coefficient functor. -/
theorem reedyRight_inverseImage
    [∀ k : ℕ, HasLimitsOfShape (matchingIndex k) C]
    [∀ k : ℕ, HasLimitsOfShape (matchingIndex k) D]
    [∀ k : ℕ, PreservesLimitsOfShape (matchingIndex k) F] :
    reedyRight (P.inverseImage F) =
      (reedyRight P).inverseImage ((whiskeringRight SimplexCategoryᵒᵖ C D).obj F) := by
  apply MorphismProperty.ext
  intro X Y f
  change (∀ k : ℕ, P (F.map (relativeMatchingMap f k))) ↔
    ∀ k : ℕ, P (relativeMatchingMap (whiskerRight f F) k)
  exact forall_congr' (fun k => relativeMatching_mem_iff F P k f)
end Matching

end CoefficientReedyTransport
end CategoryTheory.SimplicialObject
