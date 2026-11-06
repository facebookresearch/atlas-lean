/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Preferred-Q transport from exact physical short-vector transport and a single central phase. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerShortRecognition

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Exact physical short-vector transport, up to global sign, determines the actual label. -/
theorem monsterNortonShortPermutation_of_vector (e : leechIsomSubgroup)
    (r s : GriessShortIndex)
    (h : e.val (griessShortVector r) = griessShortVector s ∨
      e.val (griessShortVector r) = -griessShortVector s) :
    griessShortPermutation e r = s := by
  apply centralizer_shortVector_sign_unique
  rcases griessShortPermutation_vector e r with hp | hn
  · rcases h with h | h
    · exact Or.inl (hp.symm.trans h)
    · exact Or.inr (hp.symm.trans h)
  · rcases h with h | h
    · exact Or.inr (by
        have he := congrArg Neg.neg (hn.symm.trans h)
        simpa only [neg_neg] using he)
    · exact Or.inl (by
        have he := congrArg Neg.neg (hn.symm.trans h)
        simpa only [neg_neg] using he)

/-- Physical vector transport plus the true central coefficient certifies the whole Q image. -/
theorem monsterNortonShortQ_image_of_vector_phase (f : localFiberSubgroup)
    (r s : GriessShortIndex) (c : ZMod 2)
    (hv : f.val.2.val (griessShortVector r) = griessShortVector s ∨
      f.val.2.val (griessShortVector r) = -griessShortVector s)
    (hc : toAdd (spinConjugation f.val.1 (monsterNortonShortQ r)).coeff = c) :
    spinConjugation f.val.1 (monsterNortonShortQ r) = qCentral c * monsterNortonShortQ s := by
  have hs := monsterNortonShortPermutation_of_vector f.val.2 r s hv
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    rw [qCentral_mul_base, monsterNortonShortQ_eq, monsterNortonShortQ_eq,
      griessShortQ_image_base, hs]
  · apply toAdd.injective
    rw [qCentral_mul_coeff]
    change toAdd (spinConjugation f.val.1 (monsterNortonShortQ r)).coeff = c + 0
    rw [add_zero]
    exact hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
