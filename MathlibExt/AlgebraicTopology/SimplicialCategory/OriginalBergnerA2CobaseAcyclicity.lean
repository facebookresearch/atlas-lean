/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerIntervalCobaseWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerIntervalGenerators
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Every actual original A2 generator pushout is genuinely DK weak

The SAME small representative family and both original point labels
are retained. Every actual original attaching point map is read back
as its literal object selection. The proved full interval cobase
theorem gives weakness of the SAME supplied source map in every
genuine varying-object pushout square.

This is the A2 part of Bergner, math/0406507 v2, Lemma Push. The
transfinite combined-generator and global model conclusions are separate.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
open FixedObjects
attribute [local instance] FixedObjectModel.modelCategory

/-- Every SAME actual original A2 generator cobase change is weak on all original Homs and component objects. -/
theorem generatingIntervals_pushouts_le_weak :
    generatingIntervals.{u}.pushouts ≤ EnrichedDwyerKan.weakEquivalences := by
  rintro C D f ⟨A, B, p, g, j, hp, sq⟩
  obtain ⟨⟨⟨H, hH⟩, s⟩⟩ := hp
  have h := representative_interval H hH
  let _ : IsCofibrant H := h.2.2.1
  have hs : IsPushout (pointMap H s)
      (BergnerObjects.select (C := C) (g.obj PUnit.unit)) j f :=
    (BergnerObjects.select_readback g).symm ▸ sq.flip
  exact OriginalIntervalCobaseWeak.point_weak H s (g.obj PUnit.unit) j f hs h.2.2.2

/-- The SAME source arrow in any actual original A2 pushout is genuinely DK weak. -/
theorem weak_of_interval_isPushout {A B C D : Carrier.{u}} (i : A ⟶ B) (hi : generatingIntervals i)
    (g : A ⟶ C) (j : B ⟶ D) (f : C ⟶ D) (sq : IsPushout i g j f) :
    EnrichedDwyerKan.weakEquivalences f :=
  generatingIntervals_pushouts_le_weak _ (MorphismProperty.pushouts_mk _ sq.flip hi)

end CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
