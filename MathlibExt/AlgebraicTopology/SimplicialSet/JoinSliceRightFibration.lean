/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Quasicategory.RightFibration
public import MathlibExt.AlgebraicTopology.SimplicialSet.PushoutJoinRightHornAnodyne
public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryLiftingCore
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceFibration
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Over-slice right fibrations

An original over-slice restriction, relative to an inner fibration, is a
right fibration. In particular the over-slice of a quasicategory has a
right-fibration projection. These are the over-oriented counterparts of
the existing under-slice theorems. Both the whole join map and its fixed
right factor are the native maps of the slice adjunction.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace SSet.sliceOver

/-- The actual over-slice of a terminal ambient target is terminal. -/
def isTerminalOfIsTerminalTarget {K T : SSet.{u}} (hT : IsTerminal T)
    (f : K ⟶ T) : IsTerminal (sliceOver T f) := by
  let _ : (joinRightDivision K).IsRightAdjoint := (joinOverAdjunction K).isRightAdjoint
  exact (sliceUnder.underMkIsTerminal hT f).isTerminalObj (joinRightDivision K) (Under.mk f)

/-- The empty-factor over-slice is the original simplicial set. -/
def initialIsoOf (X : SSet.{u}) (f : (⊥_ SSet.{u}) ⟶ X) :
    sliceOver X f ≅ X :=
  eqToIso (congrArg (sliceOver X)
      (initialIsInitial.hom_ext f (initial.to X))) ≪≫ initialIso X

/-- The original empty-factor comparison has the native slice projection as its whole map. -/
@[simp]
theorem initialIsoOf_hom (X : SSet.{u}) (f : (⊥_ SSet.{u}) ⟶ X) :
    (initialIsoOf X f).hom = proj X f := by
  have h : f = initial.to X := initialIsInitial.hom_ext _ _
  subst f
  simp [initialIsoOf, initialIso_hom]

/-- Restriction at the initial factor is the original slice projection through its specified Iso. -/
def restrictInitialArrowIso {K X : SSet.{u}} (f : K ⟶ X) :
    Arrow.mk (restrict X f (initial.to K)) ≅ Arrow.mk (proj X f) :=
  Arrow.isoMk' _ _ (Iso.refl _)
    (initialIsoOf X (initial.to K ≫ f)) (by
      change proj X f = restrict X f (initial.to K) ≫
        (initialIsoOf X (initial.to K ≫ f)).hom
      rw [initialIsoOf_hom]
      exact (restrict_proj X f (initial.to K)).symm)

/-- The terminal comparison pullback is the entire original first factor. -/
def restrictionComparisonTerminalPullbackIso
    {K₀ K X T : SSet.{u}} (hT : IsTerminal T)
    (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ T) :
    pullback (map X (i ≫ f) q) (restrict T (f ≫ q) i) ≅ sliceOver X (i ≫ f) := by
  let hSource : IsTerminal (sliceOver T (f ≫ q)) := isTerminalOfIsTerminalTarget hT (f ≫ q)
  let hTarget : IsTerminal (sliceOver T (i ≫ (f ≫ q))) :=
    isTerminalOfIsTerminalTarget hT (i ≫ (f ≫ q))
  let _ : IsIso (restrict T (f ≫ q) i) := isIso_of_isTerminal hSource hTarget _
  let _ : IsIso (pullback.fst (map X (i ≫ f) q) (restrict T (f ≫ q) i)) :=
    pullback_fst_iso_of_right_iso _ _
  exact asIso (pullback.fst (map X (i ≫ f) q) (restrict T (f ≫ q) i))

/-- The terminal comparison is the original restriction through its native pullback Iso. -/
def restrictionComparisonTerminalArrowIso
    {K₀ K X T : SSet.{u}} (hT : IsTerminal T)
    (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ T) :
    Arrow.mk (restrictionComparison i f q) ≅ Arrow.mk (restrict X f i) :=
  Arrow.isoMk' _ _ (Iso.refl _) (restrictionComparisonTerminalPullbackIso hT i f q)
    (by exact (restrictionComparison_fst i f q).symm)

end SSet.sliceOver

namespace SSet

/-- The actual over-slice restriction comparison is a right fibration. -/
theorem rightFibration_sliceOver_restrictionComparison
    {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K) [Mono i]
    (f : K ⟶ X) (q : X ⟶ S) [InnerFibration q] :
    RightFibration (sliceOver.restrictionComparison i f q) where
  hasLiftingProperty_horn k hk :=
    ((sliceOver.hasLiftingProperty_pushoutJoin_iff_forall i (horn _ k).ι q).mp
      ((innerAnodyneExtensions_pushoutJoin_rightHorn k hk i) q InnerFibration.mem)) f

/-- Restricting an over-slice of a quasicategory along a monomorphism is a right fibration. -/
theorem rightFibration_sliceOver_restrict
    (X : SSet.{u}) [Quasicategory X] {K₀ K : SSet.{u}}
    (f : K ⟶ X) (i : K₀ ⟶ K) [Mono i] :
    RightFibration (sliceOver.restrict X f i) where
  hasLiftingProperty_horn k hk := by
    have h : RightFibration (sliceOver.restrictionComparison i f (terminal.from X)) :=
      rightFibration_sliceOver_restrictionComparison i f (terminal.from X)
    exact (HasLiftingProperty.iff_of_arrow_iso_right (horn _ k).ι
      (sliceOver.restrictionComparisonTerminalArrowIso
        (terminalIsTerminal : IsTerminal (⊤_ SSet.{u})) i f (terminal.from X))).mp
      (RightFibration.hasLiftingProperty_horn k hk)

/-- Projection of the actual over-slice of a quasicategory is a right fibration. -/
instance (priority := 900) rightFibration_sliceOver_proj
    (X : SSet.{u}) [Quasicategory X] {K : SSet.{u}} (f : K ⟶ X) :
    RightFibration (sliceOver.proj X f) where
  hasLiftingProperty_horn k hk := by
    have h : RightFibration (sliceOver.restrict X f (initial.to K)) :=
      rightFibration_sliceOver_restrict X f (initial.to K)
    exact (HasLiftingProperty.iff_of_arrow_iso_right (horn _ k).ι
      (sliceOver.restrictInitialArrowIso f)).mp (RightFibration.hasLiftingProperty_horn k hk)

/-- The actual over-slice of a quasicategory is a quasicategory. -/
instance (priority := 900) quasicategory_sliceOver
    (X : SSet.{u}) [Quasicategory X] {K : SSet.{u}} (f : K ⟶ X) :
    Quasicategory (sliceOver X f) :=
  quasicategory_of_rightFibration (sliceOver.proj X f)

end SSet
