/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerIntervalConverse
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerA2EquivalenceVertexRecognition

/-!
# The genuine original A1/A2 right class is exactly the full Bergner fibration class

The actual original positive-horn family gives all full original Hom
Kan fibrations. The genuine small countable interval family gives the
exact supplied original F2 vertex lifts. Conversely, genuine F1/F2 gives
full original lifts of both point maps of every actual representative
interval. No fibration-class or global-model outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
open FixedObjects OriginalWalkingArrowFreeSingleHomIso
attribute [local instance] FixedObjectModel.modelCategory
variable {E D : Carrier.{u}}

/-- Genuine original full Bergner fibrations lift against EVERY actual original small-A2 representative point map. -/
theorem localFibrations_intervals_rlp (r : E ⟶ D) (hr : Bergner.localFibrations r) :
    generatingIntervals.rlp r := by
  intro A B i hi
  obtain ⟨⟨⟨H, hH⟩, x⟩⟩ := hi
  have h := representative_interval H hH
  let _ : IsCofibrant H := h.2.2.1
  rcases x with ⟨x⟩
  cases x
  · exact OriginalBergnerIntervalConverse.source_point_lifting r hr H h.2.2.2
  · exact OriginalBergnerIntervalConverse.target_point_lifting r hr H h.2.2.2

/-- The SAME actual original combined generating right class is precisely the canonical full
Hom-Kan/component-isofibration class. -/
theorem generatingTrivialCofibrations_rlp_iff (r : E ⟶ D) :
    generatingTrivialCofibrations.rlp r ↔ Bergner.localFibrations r := by
  constructor
  · intro h
    have hh : Bergner.generatingHomHorns.rlp r := fun _ _ i hi => h i (Or.inl hi)
    have hI : generatingIntervals.rlp r := fun _ _ i hi => h i (Or.inr hi)
    exact (Bergner.localFibrations_original_vertex_iff r).mpr
      ⟨(Bergner.generatingHomHorns_rlp_iff r).mp hh, right_equivalenceVertexLifting r hI⟩
  · intro h
    have hh := (Bergner.generatingHomHorns_rlp_iff r).mpr h.1
    have hI := localFibrations_intervals_rlp r h
    rintro A B i (hi | hi)
    · exact hh i hi
    · exact hI i hi

/-- The unchanged genuine original A1/A2 right class equals the original canonical varying-object Bergner fibration
predicate. -/
theorem generatingTrivialCofibrations_rlp_eq :
    generatingTrivialCofibrations.{u}.rlp = Bergner.localFibrations := by
  ext E D r
  exact generatingTrivialCofibrations_rlp_iff r

end CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
