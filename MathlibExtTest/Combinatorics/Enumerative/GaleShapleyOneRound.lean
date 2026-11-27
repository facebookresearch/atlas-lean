/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GaleShapleyOneRound

/-! # Profiles on which the Gale–Shapley algorithm ends in one round -/

namespace MetaMathlibExt.StableMatchingSequences.GaleShapleyOneRoundTest

-- Man `i` ranks woman `i` first, so every woman is the first choice of exactly one man.
private def distinctFirstChoices : PreferenceProfile 3 :=
  (fun i => Equiv.swap 0 i, fun _ => Equiv.refl _)

example : galeShapleyRounds distinctFirstChoices = 1 := by
  rw [galeShapleyRounds_eq_one_iff _ (by decide)]
  unfold ExistsUnique
  decide

-- Every man ranks woman `0` first, so the algorithm needs more than one round.
private def sameFirstChoice : PreferenceProfile 3 :=
  (fun _ => Equiv.refl _, fun _ => Equiv.refl _)

example : galeShapleyRounds sameFirstChoice ≠ 1 := by
  rw [Ne, galeShapleyRounds_eq_one_iff _ (by decide)]
  unfold ExistsUnique
  decide

-- With one man and one woman, the algorithm always ends in one round.
example (P : PreferenceProfile 1) : galeShapleyRounds P = 1 :=
  (galeShapleyRounds_eq_one_iff P Nat.one_pos).mpr fun _ =>
    ⟨0, Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩

-- The hypothesis `0 < n` is needed: with nobody to match the algorithm takes no rounds, although
-- the condition on first choices holds vacuously.
example (P : PreferenceProfile 0) : galeShapleyRounds P ≠ 1 := by
  rw [galeShapleyRounds_of_zero]
  decide

end MetaMathlibExt.StableMatchingSequences.GaleShapleyOneRoundTest
