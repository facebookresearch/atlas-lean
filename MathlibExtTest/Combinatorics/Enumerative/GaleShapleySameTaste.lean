/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GaleShapleySameTaste

/-! # Round counts with identical men's preferences -/

namespace MetaMathlibExt.StableMatchingSequences.GaleShapleySameTasteTest

-- The public theorem needs no hypothesis on the women's rankings.
example {n : ℕ} (P : PreferenceProfile n) (h : ∀ i i' : Fin n, P.1 i = P.1 i') :
    galeShapleyRounds P = n :=
  galeShapleyRounds_of_same_taste P h

-- The common-ranking hypothesis is vacuous when there are no participants.
example (P : PreferenceProfile 0) : galeShapleyRounds P = 0 :=
  galeShapleyRounds_of_same_taste P fun i _ => i.elim0

-- The men all rank woman `2` first; the women's rankings are not all the same.
private def commonRanking : PreferenceProfile 3 :=
  (fun _ => Equiv.swap 0 2, fun j => if j = 2 then Equiv.swap 0 1 else Equiv.refl _)

example : galeShapleyRounds commonRanking = 3 :=
  galeShapleyRounds_of_same_taste commonRanking fun _ _ => rfl

end MetaMathlibExt.StableMatchingSequences.GaleShapleySameTasteTest
