/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StableMatchingSequences

/-! # A three-couple market with two stable matchings -/

namespace MetaMathlibExt.StableMatchingSequences

-- Everyone ranks participant 2 on the other side last. Among the first two couples,
-- the men prefer the identity matching and the women prefer the swap.
private def threeCoupleProfile : PreferenceProfile 3 :=
  (fun i => if i = 1 then Equiv.swap 0 1 else Equiv.refl _,
   fun j => if j = 0 then Equiv.swap 0 1 else Equiv.refl _)

private theorem stable_identity : IsStableMatching threeCoupleProfile (Equiv.refl _) := by
  rw [isStableMatching_iff]
  decide

example : IsStableMatching threeCoupleProfile (Equiv.swap 0 1) := by
  rw [isStableMatching_iff]
  decide

example (ν : Equiv.Perm (Fin 3)) (hν : IsStableMatching threeCoupleProfile ν) : ν 2 = 2 := by
  apply hellCouple_mem_all_stable threeCoupleProfile (Equiv.refl _) ν stable_identity hν 2
  exact ⟨rfl, rfl⟩

end MetaMathlibExt.StableMatchingSequences
