/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.SocialChoice.CondorcetCycle
import Mathlib.Tactic

/-! Examples and checks for `MathlibExt.GameTheory.SocialChoice.CondorcetCycle` (Atlas AP03.T01). -/

namespace MathlibExtTest.GameTheory.SocialChoice.CondorcetCycle

open MathlibExt.GameTheory.SocialChoice.CondorcetCycle
open MathlibExt.GameTheory.SocialChoice.ArrowWanted

example : ∃ P : Profile (Fin 3) (Fin 3), IsMajorityCycle P 0 1 2 :=
  exists_isMajorityCycle

example : ∃ P : Profile (Fin 3) (Fin 3),
    MajorityPrefers P 0 1 ∧ MajorityPrefers P 1 2 ∧ ¬ MajorityPrefers P 0 2 :=
  exists_majorityPrefers_not_transitive

example : ∃ P : Profile (Fin 3) (Fin 3), ∀ a, ∃ b, MajorityPrefers P b a :=
  exists_no_condorcetWinner

theorem test_cycle : IsMajorityCycle condorcetProfile 0 1 2 :=
  condorcet_cycle

theorem test_card : (supporters condorcetProfile 0 1).card = 2 :=
  condorcet_card01

theorem test_not : ¬ MajorityPrefers condorcetProfile 1 0 :=
  condorcet_nmaj10

end MathlibExtTest.GameTheory.SocialChoice.CondorcetCycle
