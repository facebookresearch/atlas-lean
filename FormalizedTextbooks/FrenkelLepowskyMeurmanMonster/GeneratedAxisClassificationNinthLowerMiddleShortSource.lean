/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerMiddleShortSourceGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerMiddleShortCertificates

/-! Complete finite middle certificates instantiate the actual original source bindings. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every nonzero middle cache value has a complete original chronological source target. -/
theorem generatedNinth_lower_middle_short_cache_covered (r : GriessShortIndex)
    (h : generatedNinthLowerMiddleShortCoefficient r ≠ 0) :
    ∃ k : Fin 4136, generatedNinthShortRowTarget k = r :=
  generatedNinth_lower_middle_short_generic_cache_covered
    generatedNinth_lower_middle_short_key_target r h

/-- Every actual middle short coefficient equals its complete original source cache divided by16. -/
theorem generatedNinth_lower_middle_short_actual
    (hrows : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
    (r : GriessShortIndex) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 r =
        (generatedNinthLowerMiddleShortCoefficient r : ℝ) / 16 :=
  generatedNinth_lower_middle_short_generic_actual
    generatedNinth_lower_middle_short_key_target
    generatedNinth_lower_middle_short_rows_covered hrows r

/-- Every incoming odd column uses the same completely bound original middle cache. -/
theorem generatedNinth_lower_incoming_actual
    (hrows : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
    (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 (Sum.inr (Sum.inr (d, i))) =
        (generatedNinthLowerIncomingCoefficient d i : ℝ) / 16 :=
  generatedNinth_lower_middle_short_actual hrows _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
