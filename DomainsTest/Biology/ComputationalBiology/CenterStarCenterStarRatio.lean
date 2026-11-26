/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.ComputationalBiology.CenterStarCenterStarRatio
import Mathlib.Tactic.NormNum

/-!
# Two-row center-star alignment

For two input strings with a positive optimum, the center-star ratio theorem implies
that the center-star alignment has optimal value.

Source: D. Gusfield, "Efficient methods for multiple sequence alignment with
guaranteed error bounds", Bulletin of Mathematical Biology 55(1):141-154,
1993, doi:10.1007/BF02460299, Lemma 3.1 and Theorem 3.1.
-/

namespace DomainsTest.Biology.ComputationalBiology.CenterStarCenterStarRatio

open WantedExt.Biology.ComputationalBiology.CenterStarWanted

example {α : Type*} [DecidableEq α] (s : Option α → Option α → ℝ)
    (hgap : s none none = 0)
    (hdiag : ∀ x : Option α, s x x = 0)
    (htria : ∀ x y z : Option α, s x z ≤ s x y + s y z)
    (hsymm : ∀ x y : Option α, s x y = s y x)
    (X : Fin 2 → List α)
    (hD_le : ∀ (U V : List α) (A : PairAlignment α),
      IsPairAlignmentOf A U V → pairDist s U V ≤ alignValue s A)
    (hD_att : ∀ U V : List α, ∃ A : PairAlignment α,
      IsPairAlignmentOf A U V ∧ pairDist s U V = alignValue s A)
    (c : Fin 2)
    (hcenter : ∀ i : Fin 2, centerTotal s X (X c) ≤ centerTotal s X (X i))
    (Ac : MSAlignment α 2)
    (hac : msErasesTo Ac X)
    (hproj : ∀ i, inducedValue s Ac c i = pairDist s (X c) (X i))
    (Astar : MSAlignment α 2)
    (hastar : msErasesTo Astar X)
    (hopt : ∀ A' : MSAlignment α 2, msErasesTo A' X →
      msaValue s Astar ≤ msaValue s A')
    (hpos : 0 < msaValue s Astar) :
    msaValue s Ac = msaValue s Astar := by
  have hratio := (centerStar_ratio s hgap hdiag htria hsymm 2 (by decide)
    X hD_le hD_att c hcenter Ac hac hproj Astar hastar hopt hpos).1
  norm_num at hratio
  apply le_antisymm _ (hopt Ac hac)
  simpa using (div_le_iff₀ hpos).mp hratio

end DomainsTest.Biology.ComputationalBiology.CenterStarCenterStarRatio
