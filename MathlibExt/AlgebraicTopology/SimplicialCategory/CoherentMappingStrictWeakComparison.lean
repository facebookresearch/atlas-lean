/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomMappingWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingStrictNaturality

/-!
# Same strict-map weak comparison on original Hom and right mapping spaces

At supplied individual original endpoints, the actual strict enriched
Hom map is weak exactly when the actual right-mapping-space map is weak,
provided both original Hom objects are Kan. This uses the proved whole
comparison square and two-out-of-three, with no model-comparison record.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.CoherentRealization.MappingStrictNaturality
open SimplicialEnrichment

/-- The same original strict enriched map is weak on a supplied Kan Hom pair exactly when it is weak on the
  actual corresponding right mapping spaces. -/
theorem map_weak_iff {C D : Carrier.{u}} (F : C ⟶ D) (x y : C)
    [SSet.KanComplex (x ⟶[SSet.{u}] y)]
    [SSet.KanComplex (F.obj x ⟶[SSet.{u}] F.obj y)] :
    SSet.realizationWeakEquivalences (map F x y) ↔
      SSet.realizationWeakEquivalences (F.map x y) := by
  have hx := HomMapping.map_weak x y
  have hy := HomMapping.map_weak (F.obj x) (F.obj y)
  calc
    _ ↔ SSet.realizationWeakEquivalences (HomMapping.map x y ≫ map F x y) :=
      (SSet.realizationWeakEquivalences.precomp_iff (HomMapping.map x y) (map F x y) hx).symm
    _ ↔ SSet.realizationWeakEquivalences (F.map x y ≫ HomMapping.map (F.obj x) (F.obj y)) := by
      rw [homComparison_naturality]
    _ ↔ _ := SSet.realizationWeakEquivalences.postcomp_iff
      (F.map x y) (HomMapping.map (F.obj x) (F.obj y)) hy

end CategoryTheory.CoherentRealization.MappingStrictNaturality
