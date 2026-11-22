/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.RightFibrationIsoLifting
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceRightFibration
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.QuasicategoryFibrations
public import MathlibExt.AlgebraicTopology.SimplicialSet.Slice

/-!
# Genuine categorical fibrations of the two original slice projections

The join slice projection is its existing right fibration, together with
the exact equivalence-edge lifting theorem. The path slice projection is
the original base change of the endpoint restriction fibration, transported
by its existing slice/pullback isomorphism. Both maps retain their original
leading projection to the ambient quasicategory.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalClosed
open scoped Simplicial

namespace SSet

/-- A right fibration with quasicategory codomain is a genuine categorical fibration. -/
theorem categoricalFibrations_of_rightFibration {X Y : SSet.{u}}
    (p : X ⟶ Y) [RightFibration p] [Quasicategory Y] :
    categoricalFibrations p :=
  (categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting p).mpr
    ⟨inferInstance, hasStrictEquivalenceLifting_of_rightFibration p⟩

/-- The original join over-slice projection is a genuine categorical fibration. -/
theorem categoricalFibrations_sliceOver_proj (H : SSet.{u}) [Quasicategory H]
    {K : SSet.{u}} (z : K ⟶ H) : categoricalFibrations (sliceOver.proj H z) :=
  categoricalFibrations_of_rightFibration (sliceOver.proj H z)

/-- The original pair of path endpoints is a genuine categorical fibration. -/
theorem categoricalFibrations_pathPair (H : SSet.{u}) [Quasicategory H] :
    categoricalFibrations (pathPair H) := by
  rw [pathPair_eq]
  exact (MorphismProperty.cancel_right_of_respectsIso categoricalFibrations
    ((pre (boundary 1).ι).app H) (ihomBoundaryOneIso H).hom).mpr
      (categoricalFibrations_pre_app_of_mono (boundary 1).ι H)

/-- The original path over-slice projection is a genuine categorical fibration. -/
theorem categoricalFibrations_pathSliceOver_proj (H : SSet.{u}) [Quasicategory H]
    (z : (Δ[0] : SSet.{u}) ⟶ H) : categoricalFibrations (pathSliceOver.proj z) := by
  let e := pathSliceOverIsoPairPullback z
  have hproj : pathSliceOver.proj z = e.hom ≫
      pullback.snd (pathPair H) (prod.lift (𝟙 H) (toDeltaZero H ≫ z)) :=
    (pullback.lift_snd _ _ _).symm
  have hpb : categoricalFibrations
      (pullback.snd (pathPair H) (prod.lift (𝟙 H) (toDeltaZero H ≫ z))) :=
    MorphismProperty.pullback_snd _ _ (categoricalFibrations_pathPair H)
  rw [hproj]
  exact (MorphismProperty.cancel_left_of_respectsIso categoricalFibrations
    e.hom _).mpr hpb

end SSet
