/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCompletionLocalizationPullback

/-!
# The same original arrow lifts into the actual localization pullback

Complete the supplied original full fixed-label functor and factor that
actual map using the original horn factorization. Its two original unit
maps and full naturality square construct the literal pullback lift.
Both whole projection equations retain the supplied original functor
and the same original replacement inclusion, without interval outcomes.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalCompletionLocalizationLift
open ScalarGroupoidCompletion
variable {O : Type u} {A C : FixedObjects O} (F : A ⟶ C)

/-- The SAME original completed functor, retaining the full original object and Hom maps. -/
abbrev completedMap : fixedObject A ⟶ fixedObject C := fixedMap F

/-- The actual full original localization pullback of that SAME completed functor's right factor. -/
abbrev object : FixedObjects O :=
  OriginalCompletionLocalizationPullback.object C (completedMap F)

/-- The actual unit square and original factorization give the SAME full pullback lift. -/
def lift : A ⟶ object F :=
  pullback.lift F
    (fixedUnit A ≫ OriginalCompletionLocalizationPullback.left C (completedMap F))
    (by
      have h := OriginalCompletionLocalizationPullback.factors C (completedMap F)
      exact (fixedUnit_naturality F).symm.trans
        ((congrArg (fun f => fixedUnit A ≫ f) h).symm.trans (Category.assoc _ _ _).symm))

/-- The actual first projection recovers the entire SAME supplied original functor. -/
theorem lift_toSource :
    lift F ≫ OriginalCompletionLocalizationPullback.toSource C (completedMap F) = F :=
  pullback.lift_fst _ _ _

/-- The actual second projection recovers the SAME whole original unit and left replacement factor. -/
theorem lift_toMiddle :
    lift F ≫ OriginalCompletionLocalizationPullback.toMiddle C (completedMap F) =
      fixedUnit A ≫ OriginalCompletionLocalizationPullback.left C (completedMap F) :=
  pullback.lift_snd _ _ _

/-- Every full original Hom coefficient recovers its SAME original first-projection map. -/
theorem lift_toSource_hom (x y : O) :
    homMap (lift F) x y ≫
      homMap (OriginalCompletionLocalizationPullback.toSource C (completedMap F)) x y = homMap F x y := by
  have h := congrArg (fun f => homMap f x y) (lift_toSource F)
  rw [homMap_comp] at h
  exact h

end CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalCompletionLocalizationLift
