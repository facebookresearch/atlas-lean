/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Fixed-baseline core comparison and scalar rectification.
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalCorePowerDiagonalSelector
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkCompletionUnitData
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.CoreComparisonFibrantBaseRectification

/-!
# Scalar factorization of the core-diagonal comparison

For a Segal space whose designated completion is also Segal, the core-diagonal comparison admits
a scalar trivial-cofibration and fibration factorization. The suffix and its projection to the
completion's ordered object-pair base are fibrations, and the prefix retains the prescribed
comparison over that base.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCompletionCoreDiagonal
open RezkCompletionRaw SegalHomotopy

/-- The whole comparison uses the one fixed baseline unit of the original raw diagonal. -/
def sameCoreComparison (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    coreDiagonal W hW ⟶
      (equivalenceSubcomplex (RezkCompletionData.completion.obj W) hHat : SSet.{u}) :=
  coreDiagonalComparison (RezkBaselineReplacement.unit.app (rawCompletion W)) hW hHat

/-- The base is literally HatW₀ × HatW₀ with its original ordered projections. -/
def sameCoreBase (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    coreDiagonal W hW ⟶
      (RezkCompletionData.completion.obj W).diagram _⦋0⦌ ⨯
        (RezkCompletionData.completion.obj W).diagram _⦋0⦌ :=
  coreDiagonalBase (RezkBaselineReplacement.unit.app (rawCompletion W)) hW

/-- The original scalar comparison is over the fixed SAME target object-pair base. -/
theorem sameCoreComparison_over_base (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    sameCoreComparison W hW hHat ≫
      coreEndpoint (RezkCompletionData.completion.obj W) hHat = sameCoreBase W hW :=
  coreDiagonalComparison_over_base _ _ _

/-- Factor this actual comparison; neither a diagonal fibration nor core weakness is supplied. -/
def sameCoreRectification (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    MorphismProperty.MapFactorizationData
      (trivialCofibrations SSet.{u}) (fibrations SSet.{u})
      (sameCoreComparison W hW hHat) :=
  SSet.coreComparisonFactorization (sameCoreComparison W hW hHat)

/-- The rectified source projection is the actual fibration factor followed by the target core
endpoint. -/
def sameRectifiedCoreBase (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    (sameCoreRectification W hW hHat).Z ⟶
      (RezkCompletionData.completion.obj W).diagram _⦋0⦌ ⨯
        (RezkCompletionData.completion.obj W).diagram _⦋0⦌ :=
  (sameCoreRectification W hW hHat).p ≫
    coreEndpoint (RezkCompletionData.completion.obj W) hHat

/-- The scalar prefix is a genuine native trivial cofibration. -/
theorem sameCoreRectification_prefix_trivialCofibration
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    trivialCofibrations SSet.{u} (sameCoreRectification W hW hHat).i :=
  (sameCoreRectification W hW hHat).hi

/-- Its prefix equation retains the actual original SAME map to HatW₀ × HatW₀. -/
theorem sameCoreRectification_prefix_over_base
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    (sameCoreRectification W hW hHat).i ≫ sameRectifiedCoreBase W hW hHat =
      sameCoreBase W hW := by
  rw [sameRectifiedCoreBase, ← Category.assoc,
    (sameCoreRectification W hW hHat).fac, sameCoreComparison_over_base]

/-- Both actual rectified maps are fibrations by the derived SAME target
component-union endpoint. No fibration of the original comparison is supplied. -/
theorem sameCoreRectification_fibrations
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    Fibration (sameCoreRectification W hW hHat).p ∧
      Fibration (sameRectifiedCoreBase W hW hHat) := by
  let : Fibration (coreEndpoint (RezkCompletionData.completion.obj W) hHat) :=
    coreEndpoint_fibration _ hHat
  exact SSet.coreComparisonFactorization_fibrations _ _

end SimplicialSpace.RezkCompletionCoreDiagonal
