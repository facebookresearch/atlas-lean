/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeIntervalBoundaryComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeIntervalEndpointComparison
import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneSystem

/-!
# Genuine small anodyne systems for the original fixed-base cylinder

The exact original source-projection interval, the genuinely small
original boundary-completed family and both whole corner laws verify
all native anodyne-system axioms. Monicity follows from the proved full
weak-mono inclusion. No full all-arrow weak-class recognition, uniform
weak-mono generation or marked model is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped Simplicial

namespace SSet.Marked

private theorem ofHoms_shrink_eq {C : Type*} [Category C] {I : Type*} [Small.{u} I]
    {X Y : I → C} (f : ∀ i, X i ⟶ Y i) :
    ofHoms (fun i : Shrink.{u} I => f ((equivShrink I).symm i)) = ofHoms f := by
  ext A D g
  constructor
  · rintro ⟨i⟩
    exact ofHoms.mk ((equivShrink I).symm i)
  · rintro ⟨i⟩
    rw [ofHoms_iff]
    exact ⟨equivShrink I i, congrArg (fun j => Arrow.mk (f j)) ((equivShrink I).left_inv i).symm⟩

/-- Every whole original Cartesian anodyne boundary corner belongs to the actual small generated left class. -/
theorem cartesianRelativeBoundary_native_boundary_left {B : SSet.{u}} {X Y : Over (max B)}
    (f : X ⟶ Y) (hf : (cartesianRelativeBoundaryCells B).rlp.llp f) :
    (cartesianRelativeBoundaryCells B).rlp.llp ((relativeIntervalCylinder (max B)).boundaryCorner f) := by
  let _ : Mono relativeIntervalWholeBoundary.{u} := relativeIntervalWholeBoundary_mono
  have h := cartesianRelativeBoundary_left_scalar_mono f hf relativeIntervalWholeBoundary.{u}
  exact ((cartesianRelativeBoundaryCells B).rlp.llp.arrow_iso_iff (relativeIntervalBoundaryCornerIso f)).mp h

/-- The complete original dual boundary-corner axiom holds against arbitrary marked right codomains. -/
theorem cocartesianRelativeBoundary_native_boundary_left {B : SSet.{u}} {X Y : Over (max B)}
    (f : X ⟶ Y) (hf : (cocartesianRelativeBoundaryCells B).rlp.llp f) :
    (cocartesianRelativeBoundaryCells B).rlp.llp ((relativeIntervalCylinder (max B)).boundaryCorner f) := by
  let _ : Mono relativeIntervalWholeBoundary.{u} := relativeIntervalWholeBoundary_mono
  have h := cocartesianRelativeBoundary_left_scalar_mono f hf relativeIntervalWholeBoundary.{u}
  exact ((cocartesianRelativeBoundaryCells B).rlp.llp.arrow_iso_iff (relativeIntervalBoundaryCornerIso f)).mp h

/-- All native axioms of a genuine small Cartesian anodyne system hold for the original fixed-base exact cylinder. -/
theorem cartesianRelativeBoundary_isAnodyneSystem (B : SSet.{u}) [Quasicategory B] :
    let _ := relativeIntervalCylinder_isExact (max B)
    (relativeIntervalCylinder (max B)).IsAnodyneSystem.{u} (cartesianRelativeBoundaryCells B).rlp.llp := by
  let _ := relativeIntervalCylinder_isExact (max B)
  refine {
    le_monomorphisms := ?_
    exists_generators := ?_
    endpoint_corner := cartesianRelativeBoundary_endpoint_left
    boundary_corner := cartesianRelativeBoundary_native_boundary_left }
  · exact (cartesianRelativeBoundary_left_le_testing B).trans inf_le_left
  · let I := RelativeBoundaryCellIndex cartesianCell.{u} B
    let _ : Small.{u} I := relativeBoundaryCellIndex_small _ B
    let rep : Shrink.{u} I → I := (equivShrink I).symm
    let f := fun s : I => (cartesianRelativeBoundaryCell B s).hom
    refine ⟨Shrink.{u} I, fun s => (cartesianRelativeBoundaryCell B (rep s)).left,
      fun s => (cartesianRelativeBoundaryCell B (rep s)).right, fun s => f (rep s), ?_, ?_⟩
    · intro s
      exact (cartesianRelativeBoundaryCells_le_testing B _ (ofHoms.mk (rep s))).1
    · exact congrArg (fun T => T.rlp.llp) (ofHoms_shrink_eq f).symm

/-- The same original cylinder has its genuine small cocartesian anodyne system with both whole endpoint and
  boundary laws. -/
theorem cocartesianRelativeBoundary_isAnodyneSystem (B : SSet.{u}) [Quasicategory B] :
    let _ := relativeIntervalCylinder_isExact (max B)
    (relativeIntervalCylinder (max B)).IsAnodyneSystem.{u} (cocartesianRelativeBoundaryCells B).rlp.llp := by
  let _ := relativeIntervalCylinder_isExact (max B)
  refine {
    le_monomorphisms := ?_
    exists_generators := ?_
    endpoint_corner := cocartesianRelativeBoundary_endpoint_left
    boundary_corner := cocartesianRelativeBoundary_native_boundary_left }
  · exact (cocartesianRelativeBoundary_left_le_testing B).trans inf_le_left
  · let I := RelativeBoundaryCellIndex cocartesianCell.{u} B
    let _ : Small.{u} I := relativeBoundaryCellIndex_small _ B
    let rep : Shrink.{u} I → I := (equivShrink I).symm
    let f := fun s : I => (cocartesianRelativeBoundaryCell B s).hom
    refine ⟨Shrink.{u} I, fun s => (cocartesianRelativeBoundaryCell B (rep s)).left,
      fun s => (cocartesianRelativeBoundaryCell B (rep s)).right, fun s => f (rep s), ?_, ?_⟩
    · intro s
      exact (cocartesianRelativeBoundaryCells_le_testing B _ (ofHoms.mk (rep s))).1
    · exact congrArg (fun T => T.rlp.llp) (ofHoms_shrink_eq f).symm

end SSet.Marked
