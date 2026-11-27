/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StableMatchingOutcastProfiles

namespace MetaMathlibExt.StableMatchingSequences

private abbrev HasOutcasts {n : ℕ} (P : PreferenceProfile n) : Prop :=
  ∃ i j : Fin n, (∀ k, k ≠ i → manRank P k j = n - 1) ∧
    (∀ k, k ≠ j → womanRank P k i = n - 1)

example : Nat.card {P : PreferenceProfile 0 // HasOutcasts P} = 0 :=
  (outcast_profiles_card 0).trans (by decide)

example : Nat.card {P : PreferenceProfile 1 // HasOutcasts P} = 1 :=
  (outcast_profiles_card 1).trans (by decide)

example : Nat.card {P : PreferenceProfile 2 // HasOutcasts P} = 14 :=
  (outcast_profiles_card 2).trans (by decide)

example : Nat.card {P : PreferenceProfile 3 // HasOutcasts P} = 5184 :=
  (outcast_profiles_card 3).trans (by decide)

-- Both diagonal pairs are outcasts when each row ranks the other index last.
example :
    let P : PreferenceProfile 2 :=
      (fun i => Equiv.swap i.rev 1, fun j => Equiv.swap j.rev 1)
    ((∀ k : Fin 2, k ≠ 0 → manRank P k 0 = 1) ∧
      (∀ k : Fin 2, k ≠ 0 → womanRank P k 0 = 1)) ∧
    ((∀ k : Fin 2, k ≠ 1 → manRank P k 1 = 1) ∧
      (∀ k : Fin 2, k ≠ 1 → womanRank P k 1 = 1)) := by
  decide

end MetaMathlibExt.StableMatchingSequences
