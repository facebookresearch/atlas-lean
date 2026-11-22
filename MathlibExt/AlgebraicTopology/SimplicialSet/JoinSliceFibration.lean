/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PushoutJoinLeftHornAnodyne
public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryLiftingCore
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Join slices and left fibrations

This file proves the under-slice form of Joyal's Theorem 3.19 and its
Corollary 3.20.  Restriction of an under-slice along a monomorphism, relative
to an inner fibration, is a left fibration.  As consequences, restriction and
projection maps for diagram slices of a quasicategory are left fibrations and
all such diagram slices are quasicategories.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet.sliceUnder

/-- The structured map to a terminal simplicial set is terminal in its under
category.  This is internal support for terminal join slices. -/
@[no_expose]
def underMkIsTerminal {K T : SSet.{u}} (hT : IsTerminal T)
    (f : K ⟶ T) : IsTerminal (Under.mk f) :=
  IsTerminal.ofUniqueHom
    (fun P ↦ Under.homMk (hT.from P.right) (hT.hom_ext _ _))
    (fun P g ↦ by
      apply StructuredArrow.hom_ext
      exact hT.hom_ext _ _)

/-- A join slice whose ambient target is terminal is terminal. -/
noncomputable def isTerminalOfIsTerminalTarget {K T : SSet.{u}}
    (hT : IsTerminal T) (f : K ⟶ T) : IsTerminal (sliceUnder T f) := by
  let _ : (joinLeftDivision K).IsRightAdjoint :=
    (joinUnderAdjunction K).isRightAdjoint
  exact (underMkIsTerminal hT f).isTerminalObj
    (joinLeftDivision K) (Under.mk f)

/-- The slice below any map from the chosen initial simplicial set is
canonically isomorphic to its target. -/
noncomputable def initialIsoOf (X : SSet.{u}) (f : (⊥_ SSet.{u}) ⟶ X) :
    sliceUnder X f ≅ X :=
  eqToIso (congrArg (sliceUnder X)
      (initialIsInitial.hom_ext f (initial.to X))) ≪≫
    initialIso X

@[simp]
lemma initialIsoOf_hom (X : SSet.{u}) (f : (⊥_ SSet.{u}) ⟶ X) :
    (initialIsoOf X f).hom = proj X f := by
  have h : f = initial.to X := initialIsInitial.hom_ext _ _
  subst f
  simp [initialIsoOf, initialIso_hom]

/-- Restriction along the unique map from the chosen initial simplicial set
is isomorphic as an arrow to the slice projection. -/
noncomputable def restrictInitialArrowIso
    {K X : SSet.{u}} (f : K ⟶ X) :
    Arrow.mk (restrict X f (initial.to K)) ≅ Arrow.mk (proj X f) :=
  Arrow.isoMk' _ _ (Iso.refl _)
    (initialIsoOf X (initial.to K ≫ f)) (by
      change proj X f = restrict X f (initial.to K) ≫
        (initialIsoOf X (initial.to K ≫ f)).hom
      rw [initialIsoOf_hom]
      exact (restrict_proj X f (initial.to K)).symm)

/-- For a terminal ambient target, the pullback occurring in the restriction
comparison is canonically isomorphic to its first factor. -/
noncomputable def restrictionComparisonTerminalPullbackIso
    {K₀ K X T : SSet.{u}} (hT : IsTerminal T)
    (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ T) :
    pullback (map X (i ≫ f) q) (restrict T (f ≫ q) i) ≅
      sliceUnder X (i ≫ f) := by
  let hSource : IsTerminal (sliceUnder T (f ≫ q)) :=
    isTerminalOfIsTerminalTarget hT (f ≫ q)
  let hTarget : IsTerminal (sliceUnder T (i ≫ (f ≫ q))) :=
    isTerminalOfIsTerminalTarget hT (i ≫ (f ≫ q))
  let _ : IsIso (restrict T (f ≫ q) i) :=
    isIso_of_isTerminal hSource hTarget _
  let _ : IsIso (pullback.fst (map X (i ≫ f) q)
      (restrict T (f ≫ q) i)) :=
    pullback_fst_iso_of_right_iso _ _
  exact asIso (pullback.fst (map X (i ≫ f) q)
    (restrict T (f ≫ q) i))

@[simp]
lemma restrictionComparisonTerminalPullbackIso_hom
    {K₀ K X T : SSet.{u}} (hT : IsTerminal T)
    (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ T) :
    (restrictionComparisonTerminalPullbackIso hT i f q).hom =
      pullback.fst (map X (i ≫ f) q) (restrict T (f ≫ q) i) := rfl

/-- For a terminal ambient target, the general restriction comparison is
isomorphic as an arrow to ordinary restriction. -/
noncomputable def restrictionComparisonTerminalArrowIso
    {K₀ K X T : SSet.{u}} (hT : IsTerminal T)
    (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ T) :
    Arrow.mk (restrictionComparison i f q) ≅
      Arrow.mk (restrict X f i) :=
  Arrow.isoMk' _ _ (Iso.refl _)
    (restrictionComparisonTerminalPullbackIso hT i f q) (by
      exact (restrictionComparison_fst i f q).symm)

end SSet.sliceUnder

namespace SSet

/-- Restriction of an under-slice along a monomorphism, relative to an inner
fibration, is a left fibration. -/
theorem leftFibration_sliceUnder_restrictionComparison
    {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K) [Mono i]
    (f : K ⟶ X) (q : X ⟶ S) [InnerFibration q] :
    LeftFibration (sliceUnder.restrictionComparison i f q) := by
  apply leftFibration_of_hasLiftingProperty_horn
  intro n k hk
  exact ((sliceUnder.hasLiftingProperty_pushoutJoin_iff_forall
    i (horn n k).ι q).mp
      ((innerAnodyneExtensions_pushoutJoin_leftHorn k hk i)
        q InnerFibration.mem)) f

/-- Restriction of an under-slice of a quasicategory along a monomorphism is
a left fibration. -/
theorem leftFibration_sliceUnder_restrict
    (X : SSet.{u}) [Quasicategory X] {K₀ K : SSet.{u}}
    (f : K ⟶ X) (i : K₀ ⟶ K) [Mono i] :
    LeftFibration (sliceUnder.restrict X f i) := by
  refine ⟨(leftFibrations.arrow_mk_iso_iff
    (sliceUnder.restrictionComparisonTerminalArrowIso
      (terminalIsTerminal : IsTerminal (⊤_ SSet.{u}))
      i f (terminal.from X))).mp ?_⟩
  exact (leftFibration_sliceUnder_restrictionComparison
    i f (terminal.from X)).mem

/-- Instance form of `leftFibration_sliceUnder_restrict`.  Its reduced
priority lets existing vertex-special instances remain preferred. -/
instance (priority := 900) leftFibration_sliceUnder_restrict_inst
    (X : SSet.{u}) [Quasicategory X] {K₀ K : SSet.{u}}
    (f : K ⟶ X) (i : K₀ ⟶ K) [Mono i] :
    LeftFibration (sliceUnder.restrict X f i) :=
  leftFibration_sliceUnder_restrict X f i

/-- The projection from an arbitrary under-slice of a quasicategory is a left
fibration. -/
theorem leftFibration_sliceUnder_proj
    (X : SSet.{u}) [Quasicategory X] {K : SSet.{u}} (f : K ⟶ X) :
    LeftFibration (sliceUnder.proj X f) := by
  refine ⟨(leftFibrations.arrow_mk_iso_iff
    (sliceUnder.restrictInitialArrowIso f)).mp ?_⟩
  exact (leftFibration_sliceUnder_restrict X f (initial.to K)).mem

/-- Instance form of `leftFibration_sliceUnder_proj`.  Its reduced priority
keeps the existing vertex-special instance preferred. -/
instance (priority := 900) leftFibration_sliceUnder_proj_inst
    (X : SSet.{u}) [Quasicategory X] {K : SSet.{u}} (f : K ⟶ X) :
    LeftFibration (sliceUnder.proj X f) :=
  leftFibration_sliceUnder_proj X f

/-- An arbitrary under-slice of a quasicategory is a quasicategory. -/
theorem quasicategory_sliceUnder_of_quasicategory
    (X : SSet.{u}) [Quasicategory X] {K : SSet.{u}} (f : K ⟶ X) :
    Quasicategory (sliceUnder X f) :=
  quasicategory_of_innerFibration (sliceUnder.proj X f)

/-- Instance form of `quasicategory_sliceUnder_of_quasicategory`.  Its reduced
priority keeps the existing vertex-special instance preferred. -/
instance (priority := 900) quasicategory_sliceUnder
    (X : SSet.{u}) [Quasicategory X] {K : SSet.{u}} (f : K ⟶ X) :
    Quasicategory (sliceUnder X f) :=
  quasicategory_sliceUnder_of_quasicategory X f

end SSet
