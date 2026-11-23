/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.GameTheory.SocialChoice.McGarveyRealization

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace MathlibExtTest.GameTheory.SocialChoice.McGarveyRealization

@[expose] public section

open MathlibExt.GameTheory.SocialChoice
open MathlibExt.GameTheory.SocialChoice.ArrowWanted

/-- The test relation on three alternatives: `0 ≻ 1` and `1 ≻ 2`,
with `0` tied against `2`. -/
def testBeats : Fin 3 → Fin 3 → Prop :=
  fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)

instance : DecidableRel testBeats :=
  fun a b => inferInstanceAs (Decidable ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)))

/-- T1: the realized profile has margins `2, 2, 0` on the three
pairs of the test relation. -/
theorem t1_testBeats_margins :
    ∃ P : Profile (Fin 3)
        ({p : Fin 3 × Fin 3 // testBeats p.1 p.2} × Bool),
      netPreference P 0 1 = 2 ∧ netPreference P 1 2 = 2 ∧
        netPreference P 0 2 = 0 := by
  obtain ⟨P, hP⟩ := exists_profile_netPreference_eq_of_beats testBeats
    (by intro a; fin_cases a <;> simp [testBeats])
    (by intro a b h; fin_cases a <;> fin_cases b <;> simp [testBeats] at h ⊢)
  refine ⟨P, ?_, ?_, ?_⟩
  · simpa [testBeats] using hP 0 1 (by decide)
  · simpa [testBeats] using hP 1 2 (by decide)
  · simpa [testBeats] using hP 0 2 (by decide)

end

end MathlibExtTest.GameTheory.SocialChoice.McGarveyRealization
