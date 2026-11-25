/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StableMatchingHellCouples

/-! # Hell-couples in stable and unstable matchings -/

namespace MetaMathlibExt.StableMatchingSequences.StableMatchingHellCouplesTest

-- Two men who both form hell-couples in the same stable matching are the same man.
example {n : ℕ} (P : PreferenceProfile n) (μ : Equiv.Perm (Fin n))
    (hμ : IsStableMatching P μ) {i i' : Fin n} (hi : IsHellCouple P μ i)
    (hi' : IsHellCouple P μ i') : i = i' :=
  hellCouple_subsingleton P μ hμ hi hi'

-- Everyone ranks participant 2 on the other side last. Among the first two couples,
-- the men prefer the identity matching and the women prefer the swap.
private def threeCoupleProfile : PreferenceProfile 3 :=
  (fun i => if i = 1 then Equiv.swap 0 1 else Equiv.refl _,
   fun j => if j = 0 then Equiv.swap 0 1 else Equiv.refl _)

private theorem stable_identity : IsStableMatching threeCoupleProfile (Equiv.refl _) := by
  rw [isStableMatching_iff]
  decide

-- In the identity matching, man 2 and woman 2 rank each other last, so they form its only
-- hell-couple.
example : {i : Fin 3 | IsHellCouple threeCoupleProfile (Equiv.refl _) i} = {2} :=
  (hellCouple_subsingleton _ _ stable_identity).eq_singleton_of_mem (show _ ∧ _ by decide)

-- Each man and woman with the same number rank each other last, and each ranks the other
-- participant of the opposite sex first.
private def mutualLastProfile : PreferenceProfile 2 :=
  (fun i => if i = 0 then Equiv.swap 0 1 else Equiv.refl _,
   fun j => if j = 0 then Equiv.swap 0 1 else Equiv.refl _)

private theorem hellCouple_zero : IsHellCouple mutualLastProfile (Equiv.refl _) 0 :=
  show _ ∧ _ by decide

private theorem hellCouple_one : IsHellCouple mutualLastProfile (Equiv.refl _) 1 :=
  show _ ∧ _ by decide

-- The stability hypothesis is needed: the identity matching has two hell-couples, and man 0
-- and woman 1 block it.
example : ¬ {i : Fin 2 | IsHellCouple mutualLastProfile (Equiv.refl _) i}.Subsingleton :=
  fun h => absurd (h hellCouple_zero hellCouple_one) (by decide)

example : ¬ IsStableMatching mutualLastProfile (Equiv.refl _) := by
  rw [isStableMatching_iff]
  decide

-- Swapping the partners marries everyone to their first choice, which is stable and has no
-- hell-couple.
example : IsStableMatching mutualLastProfile (Equiv.swap 0 1) := by
  rw [isStableMatching_iff]
  decide

example : {i : Fin 2 | IsHellCouple mutualLastProfile (Equiv.swap 0 1) i} = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr (show ∀ _, ¬ (_ ∧ _) by decide)

end MetaMathlibExt.StableMatchingSequences.StableMatchingHellCouplesTest
